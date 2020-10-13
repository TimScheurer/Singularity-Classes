package ObjectPair;

public class Pair2 implements IPair2 {
    
    //@ private represents left = leftObj;
    //@ private represents right = rightObj;
    
    private /*@ nullable */ Object leftObj;
    private /*@ nullable */ Object rightObj;

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