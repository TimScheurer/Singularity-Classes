package ObjectArrayList;

public class ArrayListClient2 implements IArrayListClient2 {

    //@ private invariant obj != null;

    private Object obj = new Object();

    public void modOne(IArrayList2 list1, IArrayList2 list2) {
        list2.insert(obj);
        Object obj = list2.get(0);
    }
}