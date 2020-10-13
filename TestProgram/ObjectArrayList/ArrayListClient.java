package ObjectArrayList;

public class ArrayListClient implements IArrayListClient {
    
    //@ private invariant obj != null;

    private Object obj = new Object();

    public void modOne(IArrayList list1, IArrayList list2) {
        list2.insert(new Object());
        Object obj = list2.get(0);
    }
}