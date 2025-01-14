package norswap.sigh.ast;

import norswap.autumn.positions.Span;
import norswap.utils.Util;

public class ArraySelectionNode extends ExpressionNode {

    public ExpressionNode start = null;
    public ExpressionNode end =null;

    public ArraySelectionNode (Span span, Object start, Object end) {
        super(span);
        if (start != null) this.start = Util.cast(start, ExpressionNode.class);
        if (end != null) this.end = Util.cast(end, ExpressionNode.class);
    }


    @Override
    public String contents () {
        String content = "[";
        if (start != null) content+=start.contents();
        content+=":";
        if (end != null) content+= end.contents();
        content+="]";
        return content;
    }
}
