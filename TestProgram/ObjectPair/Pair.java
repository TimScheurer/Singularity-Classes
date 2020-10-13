package ObjectPair;

public class Pair implements IPair {

    //@ private represents left = leftObj;
    //@ private represents right = rightObj;
    //@ private invariant leftObj != null ==> \dl_isolated_from(footprint, leftObj);
    //@ private invariant leftObj != null ==> \dl_isolated_from(footprint, rightObj);
    //@ private invariant footprint == \all_fields(this);

    private /*@ nullable */ Object leftObj;
    private /*@ nullable */ Object rightObj;

    public Pair() {
        //@ set footprint = \all_fields(this);   
    }

    public void setLeft(Object left) {
        leftObj = left;
    }

    public void setRight(Object right) {
        rightObj = right;
    }

    public Object getLeft() {
        return leftObj;
    }

    public Object getRight() {
        return rightObj;
    }
}