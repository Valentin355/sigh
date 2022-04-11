package norswap.sigh.types;

public final class SelectionType extends Type
{
    public static final SelectionType INSTANCE = new SelectionType();
    private SelectionType () {}

    @Override public String name() {
        return "SelectionType";
    }
}
