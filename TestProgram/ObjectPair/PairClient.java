package ObjectPair;

public class PairClient implements IPairClient {

    //@ private invariant val1 != null && val2 != null;

    private Object val1 = new Object();
    private Object val2 = new Object();

    public void setFirst(IPair pair1, IPair pair2) {
        pair2.setLeft(val1);
        pair2.setRight(val2);
    }

    public void swap(IPair pair) {
        Object left = pair.getLeft();
        Object right = pair.getRight();
        pair.setLeft(right);
        pair.setRight(left);
    }
}