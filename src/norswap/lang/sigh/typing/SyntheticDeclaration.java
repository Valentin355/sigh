package norswap.lang.sigh.typing;

import norswap.lang.sigh.ast.DeclarationNode;

public class SyntheticDeclaration extends DeclarationNode
{
    public enum Kind {
        TYPE,
        FUNCTION,
        VARIABLE
    }

    private final String name;
    private final Kind kind;

    public SyntheticDeclaration (String name, Kind kind) {
        super(null);
        this.name = name;
        this.kind = kind;
    }

    @Override public String name () {
        return name;
    }

    public Kind kind() {
        return kind;
    }

    @Override public String contents () {
        return name;
    }

    @Override public String declaredThing () {
        return "built-in";
    }
}
