/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.parsing;

public enum RecoveryMessageType {
    PackageNameMustBeDotSeparatedIdentifierList("Package name must be a '.'-separated identifier list"),
    QualifierNameMustBeDotSeparatedIdentifierList("Qualified name must be a '.'-separated identifier list"),

    ExpectingIdentifierInImportDirective("Expecting identifier"),

    NameExpectedForClassOrObject("Name expected"),
    TypeNameExpectedInTypeAlias("Type name expected"),
    ExpectingEqualsInTypeAlias("Expecting '='"),
    ExpectingParameterName("Expecting parameter name"),
    MissingKeywordInAnnotationTarget(null),
    MissingColonInAnnotationTarget(null),
    ExpectingTypeParameterName("Expecting type parameter name"),
    ExpectingColonBeforeUpperBound("Expecting ':' before the upper bound"),
    TypeParameterNameExpected("Type parameter name expected"),
    ParameterNameExpected("Parameter name expected"),
    ExpectingArrowToSpecifyReturnTypeOfFunctionalType("Expecting '->' to specify return type of a function type"),
    ExpectingDot("Expecting '.'"),
    ExpectingTypeName("Expecting type name"),
    ExpectingArrow("Expecting '->'"),
    ExpectingLeftParenthesisInPropertyComponent("Expecting '('"),
    ExpectingVariableNameInFor("Expecting a variable name"),
    ExpectingIn("Expecting 'in'"),
    ExpectingLeftParenthesisInTryCatch("Expecting '('"),
    ExpectingRightParenthesisInTryCatch("Expecting ')'"),
    ExpectingConditionInParentheses("Expecting a condition in parentheses '(...)'"),
    ExpectingArgumentList("Expecting an argument list"),
    ExpectingRightParenthesisInArgumentList("Expecting ')'"),
    ExpectingLeftParenthesisToOpenLoopRange("Expecting '(' to open a loop range"),

    MissingRightAngleBracketInTypeParameterListInClassOrObject("Missing '>'"),
    MissingRightAngleBracketInTypeParameterListInTypeAlias("Missing '>'"),
    MissingRightAngleBracketInTypeParameterListInProperty("Missing '>'"),
    MissingRightAngleBracketInTypeParameterListInFunction1("Missing '>'"),
    MissingRightAngleBracketInTypeParameterListInFunction2("Missing '>'"),

    ExpectingNameInFunctionLiteralParameterListInMultiDeclaration("Expecting a name"),
    ExpectingNameInForInMultiDeclaration("Expecting a name"),
    ExpectingNameInPropertyInMultiDeclaration("Expecting a name"),

    ExpectingRightParenthesisInMultiDeclaration("Expecting ')'"),
    ExpectingRightParenthesisInValueParameterList("Expecting ')'"),
    ExpectingParameterNameInPropertyComponent("Expecting a parameter name"),
    ExpectingFunctionName(null),
    ExpectingPropertyName(null),

    ExpectingClosingQuote("Expecting '\"'"),
    ExpectingName("Expecting a name"),
    ExpectingRightParenthesis("Expecting ')'"),
    ExpectingLeftBrace("Expecting '{'"),
    ExpectingRightBrace("Expecting '}'"),
    ExpectingLeftBracket("Expecting '['"),
    ExpectingRightBracket("Expecting ']'"),
    ExpectingIdentifier("Expecting an identifier"),
    ArrowIsExpected("An -> is expected"),
    ExpectingWhileFollowedByPostCondition("Expecting 'while' followed by a post-condition"),
    ExpectingRightBracketToCloseAnnotationList("Expecting ']' to close the annotation list"),
    ExpectingRightBraceToCloseEnumClassBody("Expecting '}' to close enum class body"),
    ExpectingClassBody("Expecting a class body"),
    MissingRightBrace("Missing '}'"),
    ExpectingLeftBraceToOpenBlock("Expecting '{' to open a block")
    ;

    public final String message;

    RecoveryMessageType(String message) {
        this.message = message;
    }
}
