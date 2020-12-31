package norswap.lang.sigh.ast;

public enum BinaryOperator
{
    MULTIPLY("*"),
    DIVIDE("/"),
    REMAINDER("%"),
    ADD("+"),
    SUBTRACT("-"),
    EQUALITY("=="),
    NOT_EQUALS("!="),
    GREATER(">"),
    LOWER("<"),
    GREATER_EQUAL(">="),
    LOWER_EQUAL("<="),
    AND("&&"),
    OR("||"),
    ASSIGN("=");

    public final String string;

    BinaryOperator (String string) {
        this.string = string;
    }
}
