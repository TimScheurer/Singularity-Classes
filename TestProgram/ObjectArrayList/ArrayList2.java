package ObjectArrayList;

public class ArrayList2 implements IArrayList2 {
    
    //@ private represents theList = (\seq_def int i; 0; size; list[i]);
    //@ private invariant size == theList.length;
    //@ private invariant size <= list.length && size >= 0;
    //@ private invariant list.length == 16;
    //@ private invariant \typeof(list) == \type(Object[]);

    private Object[] list = new Object[16];
    private int size = 0;

    public void insert(Object obj) {
        list[size++] = obj;
    }

    public Object get(int index) {
        return list[index];
    }

    public int size() {
        return size;
    }
}