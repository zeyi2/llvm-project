//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "MissingEndComparisonCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Lexer.h"

using namespace clang::ast_matchers;

namespace clang::tidy::bugprone {

namespace {

static constexpr llvm::StringRef IteratorAlgorithms[] = {
    "::std::find",          "::std::find_if",
    "::std::find_if_not",   "::std::search",
    "::std::search_n",      "::std::find_end",
    "::std::find_first_of", "::std::lower_bound",
    "::std::upper_bound",   "::std::partition_point",
    "::std::min_element",   "::std::max_element",
    "::std::adjacent_find", "::std::is_sorted_until"};

static constexpr llvm::StringRef RangeAlgorithms[] = {
    "::std::ranges::find",        "::std::ranges::find_if",
    "::std::ranges::find_if_not", "::std::ranges::lower_bound",
    "::std::ranges::upper_bound", "::std::ranges::min_element",
    "::std::ranges::max_element"};

} // namespace

void MissingEndComparisonCheck::registerMatchers(MatchFinder *Finder) {
  const auto StdAlgoCall = callExpr(
      callee(functionDecl(hasAnyName(IteratorAlgorithms), isInStdNamespace())));

  const auto RangesCall = cxxOperatorCallExpr(
      hasOverloadedOperatorName("()"),
      hasArgument(0, declRefExpr(to(
                         varDecl(hasAnyName(RangeAlgorithms)).bind("cpo")))));

  const auto AnyAlgoCall =
      getLangOpts().CPlusPlus20
          ? expr(anyOf(StdAlgoCall, RangesCall)).bind("algoCall")
          : expr(StdAlgoCall).bind("algoCall");

  // Captures implicit pointer-to-bool casts and operator bool() calls.
  const auto DirectBoolUsage = expr(anyOf(
      implicitCastExpr(hasCastKind(CK_PointerToBoolean),
                       hasSourceExpression(ignoringParenImpCasts(AnyAlgoCall))),
      cxxMemberCallExpr(callee(cxxConversionDecl(returns(booleanType()))),
                        on(ignoringParenImpCasts(AnyAlgoCall)))));

  // Captures variable usage: `auto it = std::find(...); if (it)`
  // FIXME: This only handles variables initialized directly by the algorithm.
  // We may need to introduce more accurate dataflow analysis in the future.
  const auto VarWithAlgoInit =
      varDecl(hasInitializer(ignoringParenImpCasts(AnyAlgoCall))).bind("itVar");

  const auto VariableBoolUsage = expr(anyOf(
      implicitCastExpr(hasCastKind(CK_PointerToBoolean),
                       hasSourceExpression(ignoringParenImpCasts(
                           declRefExpr(to(VarWithAlgoInit)).bind("itRef")))),
      cxxMemberCallExpr(callee(cxxConversionDecl(returns(booleanType()))),
                        on(ignoringParenImpCasts(
                            declRefExpr(to(VarWithAlgoInit)).bind("itRef"))))));

  Finder->addMatcher(DirectBoolUsage.bind("boolOp"), this);
  Finder->addMatcher(VariableBoolUsage.bind("boolOp"), this);
}

void MissingEndComparisonCheck::check(const MatchFinder::MatchResult &Result) {
  const auto *Call = Result.Nodes.getNodeAs<CallExpr>("algoCall");
  const auto *BoolOp = Result.Nodes.getNodeAs<Expr>("boolOp");
  const auto *CPO = Result.Nodes.getNodeAs<VarDecl>("cpo");

  if (!Call || !BoolOp)
    return;

  std::string EndExprText;

  if (!CPO) {
    if (Call->getNumArgs() < 2)
      return;

    const Expr *EndArg = Call->getArg(1);
    // Filters nullptr, we assume the intent might be a valid check against null
    if (EndArg->IgnoreParenImpCasts()->isNullPointerConstant(
            *Result.Context, Expr::NPC_ValueDependentIsNull))
      return;

    EndExprText = Lexer::getSourceText(
                      CharSourceRange::getTokenRange(EndArg->getSourceRange()),
                      *Result.SourceManager, Result.Context->getLangOpts())
                      .str();
  } else {
    const FunctionDecl *Callee = Call->getDirectCallee();
    if (!Callee)
      return;

    // In std::ranges, Iterator-based overloads (Iter, Sent, Val, Proj) have
    // more parameters than Range-based overloads (Range, Val, Proj).
    // Range-based typically has 3, Iterator-based has 4.
    bool IsIterPair = Callee->getNumParams() >= 4;

    if (IsIterPair) {
      if (Call->getNumArgs() < 3)
        return;
      // find(CPO, Iter, Sent, Val, Proj) -> Sent is Arg 2.
      const Expr *EndArg = Call->getArg(2);
      EndExprText =
          Lexer::getSourceText(
              CharSourceRange::getTokenRange(EndArg->getSourceRange()),
              *Result.SourceManager, Result.Context->getLangOpts())
              .str();
    } else {
      if (Call->getNumArgs() < 2)
        return;
      // find(CPO, Range, Val, Proj) -> Range is Arg 1.
      const Expr *RangeArg = Call->getArg(1);
      const StringRef RangeText = Lexer::getSourceText(
          CharSourceRange::getTokenRange(RangeArg->getSourceRange()),
          *Result.SourceManager, Result.Context->getLangOpts());
      if (!RangeText.empty())
        EndExprText = "std::ranges::end(" + RangeText.str() + ")";
    }
  }

  if (EndExprText.empty())
    return;

  bool IsNegated = false;
  const UnaryOperator *NotOp = nullptr;
  const Expr *CurrentExpr = BoolOp;
  while (true) {
    auto Parents = Result.Context->getParents(*CurrentExpr);
    if (Parents.empty())
      break;
    if (const auto *P = Parents[0].get<ParenExpr>()) {
      CurrentExpr = P;
      continue;
    }
    if (const auto *U = Parents[0].get<UnaryOperator>()) {
      if (U->getOpcode() == UO_LNot) {
        NotOp = U;
        IsNegated = true;
      }
    }
    break;
  }

  const auto Diag =
      diag(BoolOp->getBeginLoc(),
           "result of standard algorithm used in boolean context; did "
           "you mean to compare with the end iterator?");

  if (IsNegated) {
    // !it -> (it == end)
    Diag << FixItHint::CreateRemoval(
        CharSourceRange::getTokenRange(NotOp->getOperatorLoc()));
    Diag << FixItHint::CreateInsertion(BoolOp->getBeginLoc(), "(");
    Diag << FixItHint::CreateInsertion(
        Lexer::getLocForEndOfToken(BoolOp->getEndLoc(), 0,
                                   *Result.SourceManager,
                                   Result.Context->getLangOpts()),
        " == " + EndExprText + ")");
  } else {
    // it -> (it != end)
    Diag << FixItHint::CreateInsertion(BoolOp->getBeginLoc(), "(");
    Diag << FixItHint::CreateInsertion(
        Lexer::getLocForEndOfToken(BoolOp->getEndLoc(), 0,
                                   *Result.SourceManager,
                                   Result.Context->getLangOpts()),
        " != " + EndExprText + ")");
  }
}

} // namespace clang::tidy::bugprone
