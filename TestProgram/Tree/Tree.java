package Tree;

public class Tree implements ITree {

    //@ private invariant left != this && right != this;
    //@ private invariant (left != right) || (left == null && right == null);
    //@ private invariant left != null ==> \invariant_for(left); 
    //@ private invariant right != null ==> \invariant_for(right);
    //@ private invariant footprint == ((left != null && right != null) ? \set_union(\set_union(\all_fields(this), left.footprint), right.footprint) : (left == null ? (right == null ? \all_fields(this) : \set_union(\all_fields(this), right.footprint)) : \set_union(\all_fields(this), left.footprint)));

    //@ private represents value = val;
    //@ private represents leftTree = left;
    //@ private represents rightTree = right;

    private /*@ nullable */ ITree left;
    private /*@ nullable */ ITree right;
    public int val;

    public Tree(int val) {
        this.val = val;
        //@ set footprint = \all_fields(this);
    }

    public void increment() {
        val += 1;
        if (left != null) left.increment();
        if (right != null) right.increment();
    }

    public int getVal() {
        return val;
    }

    public boolean isUniform(int val) {
        boolean leftBool = (left == null) || left.isUniform(val);
        boolean rightBool = (right == null) || right.isUniform(val);
        return (this.val == val) && leftBool && rightBool;
    }
}