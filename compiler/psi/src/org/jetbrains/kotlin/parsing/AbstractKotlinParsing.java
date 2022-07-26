/*
 * Copyright 2010-2015 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.jetbrains.kotlin.parsing;

import com.intellij.lang.PsiBuilder;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.tree.TokenSet;
import com.intellij.util.containers.Stack;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.TestOnly;
import org.jetbrains.kotlin.lexer.KtKeywordToken;
import org.jetbrains.kotlin.lexer.KtToken;
import org.jetbrains.kotlin.lexer.KtTokens;
import org.jetbrains.kotlin.utils.strings.StringsKt;

import java.util.HashMap;
import java.util.Map;

import static org.jetbrains.kotlin.lexer.KtTokens.*;
import static org.jetbrains.kotlin.parsing.KotlinExpressionParsing.*;
import static org.jetbrains.kotlin.parsing.KotlinParsing.*;

/*package*/ abstract class AbstractKotlinParsing {
    private static final Map<String, KtKeywordToken> SOFT_KEYWORD_TEXTS = new HashMap<>();

    static {
        for (IElementType type : KtTokens.SOFT_KEYWORDS.getTypes()) {
            KtKeywordToken keywordToken = (KtKeywordToken) type;
            assert keywordToken.isSoft();
            SOFT_KEYWORD_TEXTS.put(keywordToken.getValue(), keywordToken);
        }
    }

    static {
        for (IElementType token : KtTokens.KEYWORDS.getTypes()) {
            assert token instanceof KtKeywordToken : "Must be KtKeywordToken: " + token;
            assert !((KtKeywordToken) token).isSoft() : "Must not be soft: " + token;
        }
    }

    protected final SemanticWhitespaceAwarePsiBuilder myBuilder;

    public AbstractKotlinParsing(SemanticWhitespaceAwarePsiBuilder builder) {
        this.myBuilder = builder;
    }

    protected IElementType getLastToken() {
        int i = 1;
        int currentOffset = myBuilder.getCurrentOffset();
        while (i <= currentOffset && WHITE_SPACE_OR_COMMENT_BIT_SET.contains(myBuilder.rawLookup(-i))) {
            i++;
        }
        return myBuilder.rawLookup(-i);
    }

    protected PsiBuilder.Marker mark() {
        return myBuilder.mark();
    }

    protected void error(String message) {
        myBuilder.error(message);
    }

    protected boolean expect(KtToken expectation, RecoveryMessageType recoveryMessageType) {
        return expect(expectation, recoveryMessageType, null);
    }

    protected boolean expect(KtToken expectation, RecoveryMessageType recoveryMessageType, TokenSet recoveryTokens) {
        if (expect(expectation)) {
            return true;
        }

        TokenSet tokens = recoveryTokens != null ? recoveryTokens : getRecoveryTokenSet(recoveryMessageType);
        errorWithRecovery(recoveryMessageType.message, tokens);

        return false;
    }

    protected boolean expect(KtToken expectation) {
        if (at(expectation)) {
            advance(); // expectation
            return true;
        }

        if (expectation == KtTokens.IDENTIFIER && "`".equals(myBuilder.getTokenText())) {
            advance();
        }

        return false;
    }

    protected static TokenSet getRecoveryTokenSet(RecoveryMessageType recoveryMessageType) {
        switch (recoveryMessageType) {
            case PackageNameMustBeDotSeparatedIdentifierList:
                return PACKAGE_NAME_RECOVERY_SET;
            case QualifierNameMustBeDotSeparatedIdentifierList:
                return TokenSet.create(AS_KEYWORD, DOT, EOL_OR_SEMICOLON);
            case ExpectingIdentifierInImportDirective:
                return TokenSet.create(SEMICOLON);
            case NameExpectedForClassOrObject:
                return TokenSet.orSet(TokenSet.create(LT, LPAR, COLON, LBRACE), TOP_LEVEL_DECLARATION_FIRST);
            case TypeNameExpectedInTypeAlias:
                return TokenSet.orSet(TokenSet.create(LT, EQ, SEMICOLON), TOP_LEVEL_DECLARATION_FIRST);
            case ExpectingEqualsInTypeAlias:
                return TokenSet.orSet(TOP_LEVEL_DECLARATION_FIRST, TokenSet.create(SEMICOLON));
            case ExpectingParameterName:
                return TokenSet.create(ARROW);
            case ExpectingTypeParameterName:
                return TokenSet.orSet(TokenSet.create(COLON, COMMA, LBRACE, RBRACE), TYPE_REF_FIRST);
            case ExpectingColonBeforeUpperBound:
                return TokenSet.orSet(TokenSet.create(LBRACE, RBRACE), TYPE_REF_FIRST);
            case ParameterNameExpected:
                return TokenSet.create(COLON, EQ, COMMA, RPAR, VAL_KEYWORD, VAR_KEYWORD);
            case ExpectingArrowToSpecifyReturnTypeOfFunctionalType:
                return TYPE_REF_FIRST;
            case ExpectingDot:
                return TokenSet.create(IDENTIFIER, LBRACE, RBRACE);
            case ExpectingTypeName:
                return TokenSet.orSet(EXPRESSION_FIRST, KotlinExpressionParsing.EXPRESSION_FOLLOW, DECLARATION_FIRST);
            case ExpectingArrow:
                return WHEN_CONDITION_RECOVERY_SET;
            case ExpectingLeftParenthesisInPropertyComponent:
                return TokenSet.create(RPAR, IDENTIFIER, COLON, LBRACE, EQ);
            case ExpectingVariableNameInFor:
                return TokenSet.create(COLON, IN_KEYWORD);
            case ExpectingIn:
                return TokenSet.create(LPAR, LBRACE, RPAR);
            case ExpectingLeftParenthesisInTryCatch:
            case ExpectingRightParenthesisInTryCatch:
                return TRY_CATCH_RECOVERY_TOKEN_SET;
            case ExpectingConditionInParentheses:
            case ExpectingLeftParenthesisToOpenLoopRange:
                return EXPRESSION_FIRST;
            case ExpectingArgumentList:
            case ExpectingRightParenthesisInArgumentList:
                return EXPRESSION_FOLLOW;
            case MissingRightAngleBracketInTypeParameterListInClassOrObject:
            case MissingRightAngleBracketInTypeParameterListInTypeAlias:
                return TYPE_PARAMETER_GT_RECOVERY_SET;
            case MissingRightAngleBracketInTypeParameterListInProperty:
                return TokenSet.create(IDENTIFIER, EQ, COLON, SEMICOLON);
            case MissingRightAngleBracketInTypeParameterListInFunction1:
                return TokenSet.create(LBRACKET, LBRACE, RBRACE, LPAR);
            case MissingRightAngleBracketInTypeParameterListInFunction2:
                return TokenSet.orSet(TokenSet.create(LPAR), VALUE_PARAMETERS_FOLLOW_SET);
            case ExpectingNameInFunctionLiteralParameterListInMultiDeclaration:
                return TokenSet.orSet(TOKEN_SET_TO_FOLLOW_AFTER_DESTRUCTURING_DECLARATION_IN_LAMBDA, PARAMETER_NAME_RECOVERY_SET);
            case ExpectingNameInForInMultiDeclaration:
                return TokenSet.orSet(IN_KEYWORD_L_BRACE_SET, PARAMETER_NAME_RECOVERY_SET);
            case ExpectingNameInPropertyInMultiDeclaration:
                return TokenSet.orSet(PROPERTY_NAME_FOLLOW_SET, PARAMETER_NAME_RECOVERY_SET);
            case ExpectingParameterNameInPropertyComponent:
                return TokenSet.create(RPAR, COLON, LBRACE, EQ);
            case MissingColonInAnnotationTarget:
                return TokenSet.create(IDENTIFIER, RBRACKET, LBRACKET);
            case ExpectingFunctionName:
                return TokenSet.orSet(TokenSet.create(LT, LPAR, RPAR, COLON, EQ), LBRACE_RBRACE_SET, TOP_LEVEL_DECLARATION_FIRST);
            case ExpectingPropertyName:
                return TokenSet.orSet(PROPERTY_NAME_FOLLOW_SET, LBRACE_RBRACE_SET, TOP_LEVEL_DECLARATION_FIRST);
            case TypeParameterNameExpected:
                return TokenSet.EMPTY;
            case MissingKeywordInAnnotationTarget:
            case ExpectingClosingQuote:
            case ExpectingName:
            case ExpectingRightParenthesis:
            case ExpectingLeftBrace:
            case ExpectingRightBrace:
            case ExpectingLeftBracket:
            case ExpectingRightBracket:
            case ExpectingIdentifier:
            case ArrowIsExpected:
            case ExpectingWhileFollowedByPostCondition:
            case ExpectingRightBracketToCloseAnnotationList:
            case ExpectingRightBraceToCloseEnumClassBody:
            case ExpectingClassBody:
            case MissingRightBrace:
            case ExpectingLeftBraceToOpenBlock:
                return null;
            default:
                throw new IllegalStateException("Unknown recovery set type: " + recoveryMessageType);
        }
    }

    protected void expectNoAdvance(KtToken expectation, String message) {
        if (at(expectation)) {
            advance(); // expectation
            return;
        }

        error(message);
    }

    protected void errorWithRecovery(String message, TokenSet recoverySet) {
        IElementType tt = tt();
        if (recoverySet == null ||
            recoverySet.contains(tt) ||
            tt == LBRACE || tt == RBRACE ||
            (recoverySet.contains(EOL_OR_SEMICOLON) && (eof() || tt == SEMICOLON || myBuilder.newlineBeforeCurrentToken()))) {
            error(message);
        }
        else {
            errorAndAdvance(message);
        }
    }

    protected void errorAndAdvance(String message) {
        errorAndAdvance(message, 1);
    }

    protected void errorAndAdvance(String message, int advanceTokenCount) {
        PsiBuilder.Marker err = mark();
        advance(advanceTokenCount);
        err.error(message);
    }

    protected boolean eof() {
        return myBuilder.eof();
    }

    protected void advance() {
        // TODO: how to report errors on bad characters? (Other than highlighting)
        myBuilder.advanceLexer();
    }

    protected void advance(int advanceTokenCount) {
        for (int i = 0; i < advanceTokenCount; i++) {
            advance(); // erroneous token
        }
    }

    protected void advanceAt(IElementType current) {
        assert _at(current);
        myBuilder.advanceLexer();
    }

    protected IElementType tt() {
        return myBuilder.getTokenType();
    }

    /**
     * Side-effect-free version of at()
     */
    protected boolean _at(IElementType expectation) {
        IElementType token = tt();
        return tokenMatches(token, expectation);
    }

    private boolean tokenMatches(IElementType token, IElementType expectation) {
        if (token == expectation) return true;
        if (expectation == EOL_OR_SEMICOLON) {
            if (eof()) return true;
            if (token == SEMICOLON) return true;
            if (myBuilder.newlineBeforeCurrentToken()) return true;
        }
        return false;
    }

    protected boolean at(IElementType expectation) {
        if (_at(expectation)) return true;
        IElementType token = tt();
        if (token == IDENTIFIER && expectation instanceof KtKeywordToken) {
            KtKeywordToken expectedKeyword = (KtKeywordToken) expectation;
            if (expectedKeyword.isSoft() && expectedKeyword.getValue().equals(myBuilder.getTokenText())) {
                myBuilder.remapCurrentToken(expectation);
                return true;
            }
        }
        if (expectation == IDENTIFIER && token instanceof KtKeywordToken) {
            KtKeywordToken keywordToken = (KtKeywordToken) token;
            if (keywordToken.isSoft()) {
                myBuilder.remapCurrentToken(IDENTIFIER);
                return true;
            }
        }
        return false;
    }

    /**
     * Side-effect-free version of atSet()
     */
    protected boolean _atSet(TokenSet set) {
        IElementType token = tt();
        if (set.contains(token)) return true;
        if (set.contains(EOL_OR_SEMICOLON)) {
            if (eof()) return true;
            if (token == SEMICOLON) return true;
            if (myBuilder.newlineBeforeCurrentToken()) return true;
        }
        return false;
    }

    protected boolean atSet(TokenSet set) {
        if (_atSet(set)) return true;
        IElementType token = tt();
        if (token == IDENTIFIER) {
            KtKeywordToken keywordToken = SOFT_KEYWORD_TEXTS.get(myBuilder.getTokenText());
            if (set.contains(keywordToken)) {
                myBuilder.remapCurrentToken(keywordToken);
                return true;
            }
        }
        else {
            // We know at this point that <code>set</code> does not contain <code>token</code>
            if (set.contains(IDENTIFIER) && token instanceof KtKeywordToken) {
                if (((KtKeywordToken) token).isSoft()) {
                    myBuilder.remapCurrentToken(IDENTIFIER);
                    return true;
                }
            }
        }
        return false;
    }

    protected IElementType lookahead(int k) {
        return myBuilder.lookAhead(k);
    }

    protected boolean consumeIf(KtToken token) {
        if (at(token)) {
            advance(); // token
            return true;
        }
        return false;
    }

    // TODO: Migrate to predicates
    protected void skipUntil(TokenSet tokenSet) {
        boolean stopAtEolOrSemi = tokenSet.contains(EOL_OR_SEMICOLON);
        while (!eof() && !tokenSet.contains(tt()) && !(stopAtEolOrSemi && at(EOL_OR_SEMICOLON))) {
            advance();
        }
    }

    protected void errorUntil(String message, TokenSet tokenSet) {
        assert tokenSet.contains(LBRACE) : "Cannot include LBRACE into error element!";
        assert tokenSet.contains(RBRACE) : "Cannot include RBRACE into error element!";
        PsiBuilder.Marker error = mark();
        skipUntil(tokenSet);
        error.error(message);
    }

    protected static void errorIf(PsiBuilder.Marker marker, boolean condition, String message) {
        if (condition) {
            marker.error(message);
        }
        else {
            marker.drop();
        }
    }

    protected class OptionalMarker {
        private final PsiBuilder.Marker marker;
        private final int offset;

        public OptionalMarker(boolean actuallyMark) {
            marker = actuallyMark ? mark() : null;
            offset = myBuilder.getCurrentOffset();
        }

        public void done(IElementType elementType) {
            if (marker == null) return;
            marker.done(elementType);
        }

        public void error(String message) {
            if (marker == null) return;
            if (offset == myBuilder.getCurrentOffset()) {
                marker.drop(); // no empty errors
            }
            else {
                marker.error(message);
            }
        }

        public void drop() {
            if (marker == null) return;
            marker.drop();
        }
    }

    protected int matchTokenStreamPredicate(TokenStreamPattern pattern) {
        PsiBuilder.Marker currentPosition = mark();
        Stack<IElementType> opens = new Stack<>();
        int openAngleBrackets = 0;
        int openBraces = 0;
        int openParentheses = 0;
        int openBrackets = 0;
        while (!eof()) {
            if (pattern.processToken(
                    myBuilder.getCurrentOffset(),
                    pattern.isTopLevel(openAngleBrackets, openBrackets, openBraces, openParentheses))) {
                break;
            }
            if (at(LPAR)) {
                openParentheses++;
                opens.push(LPAR);
            }
            else if (at(LT)) {
                openAngleBrackets++;
                opens.push(LT);
            }
            else if (at(LBRACE)) {
                openBraces++;
                opens.push(LBRACE);
            }
            else if (at(LBRACKET)) {
                openBrackets++;
                opens.push(LBRACKET);
            }
            else if (at(RPAR)) {
                openParentheses--;
                if (opens.isEmpty() || opens.pop() != LPAR) {
                    if (pattern.handleUnmatchedClosing(RPAR)) {
                        break;
                    }
                }
            }
            else if (at(GT)) {
                openAngleBrackets--;
            }
            else if (at(RBRACE)) {
                openBraces--;
            }
            else if (at(RBRACKET)) {
                openBrackets--;
            }
            advance(); // skip token
        }

        currentPosition.rollbackTo();

        return pattern.result();
    }

    protected boolean eol() {
        return myBuilder.newlineBeforeCurrentToken() || eof();
    }

    protected static void closeDeclarationWithCommentBinders(@NotNull PsiBuilder.Marker marker, @NotNull IElementType elementType, boolean precedingNonDocComments) {
        marker.done(elementType);
        marker.setCustomEdgeTokenBinders(precedingNonDocComments ? PrecedingCommentsBinder.INSTANCE : PrecedingDocCommentsBinder.INSTANCE,
                                         TrailingCommentsBinder.INSTANCE);
    }

    protected abstract KotlinParsing create(SemanticWhitespaceAwarePsiBuilder builder);

    protected KotlinParsing createTruncatedBuilder(int eofPosition) {
        return create(new TruncatedSemanticWhitespaceAwarePsiBuilder(myBuilder, eofPosition));
    }

    protected class At extends AbstractTokenStreamPredicate {

        private final IElementType lookFor;
        private final boolean topLevelOnly;

        public At(IElementType lookFor, boolean topLevelOnly) {
            this.lookFor = lookFor;
            this.topLevelOnly = topLevelOnly;
        }

        public At(IElementType lookFor) {
            this(lookFor, true);
        }

        @Override
        public boolean matching(boolean topLevel) {
            return (topLevel || !topLevelOnly) && at(lookFor);
        }

    }

    protected class AtSet extends AbstractTokenStreamPredicate {
        private final TokenSet lookFor;
        private final TokenSet topLevelOnly;

        public AtSet(TokenSet lookFor, TokenSet topLevelOnly) {
            this.lookFor = lookFor;
            this.topLevelOnly = topLevelOnly;
        }

        public AtSet(TokenSet lookFor) {
            this(lookFor, lookFor);
        }

        @Override
        public boolean matching(boolean topLevel) {
            return (topLevel || !atSet(topLevelOnly)) && atSet(lookFor);
        }
    }

    @SuppressWarnings("UnusedDeclaration")
    @TestOnly
    public String currentContext() {
        return StringsKt.substringWithContext(myBuilder.getOriginalText(), myBuilder.getCurrentOffset(), myBuilder.getCurrentOffset(), 20);
    }
}
