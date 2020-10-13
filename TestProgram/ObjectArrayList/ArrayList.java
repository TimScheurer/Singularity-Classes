package ObjectArrayList;

public class ArrayList implements IArrayList {
    
    //@ private invariant footprint == \set_union(\all_fields(this), \all_fields(list));
    //@ private represents theList = (\seq_def int i; 0; size; list[i]);
    //@ private invariant size == theList.length;
    //@ private invariant size <= list.length && size >= 0;
    //@ private invariant list.length == 16;    
    //@ private invariant (\forall int i; 0 <= i && i < theList.length; (Object)theList[i] != null);
    //@ private invariant \typeof(list) == \type(Object[]);
    //@ private invariant (\forall int i; 0 <= i && i < list.length; \dl_isolated_from(footprint, list[i]);


    private Object[] list = new Object[16];
    private int size = 0;

    public ArrayList() {
        //@ set footprint = \set_union(\all_fields(this), \all_fields(list));
    }

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