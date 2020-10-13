package Tree;

public class Tree2 implements ITree22 {

    //@ private invariant left != this && right != this;
    //@ private invariant (left != right) || (left == null && right == null);
    //@ private invariant left != null ==> \invariant_for(left); 
    //@ private invariant right != null ==> \invariant_for(right);
    //@ private invariant footprint == ((left != null && right != null) ? \set_union(\set_union(\all_fields(this), \singleton(left.footprint)), \singleton(right.footprint)) : (left == null ? (right == null ? \all_fields(this) : \set_union(\all_fields(this), \singleton(right.footprint))) : \set_union(\all_fields(this), \singleton(left.footprint))));

    //@ private invariant left != null ==> \disjoint(\singleton(val), left.footprint);
    //@ private invariant right != null ==> \disjoint(\singleton(val), right.footprint);

    //@ private represents value = val;
    //@ private represents leftTree = left;
    //@ private represents rightTree = right;

    private /*@ nullable */ ITree2 left;
    private /*@ nullable */ ITree2 right;
    public int val;

    public Tree2(int val) {
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