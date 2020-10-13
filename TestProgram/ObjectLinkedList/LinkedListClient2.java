package ObjectLinkedList;

public class LinkedListClient2 implements ILinkedListClient2 {
    
    // @ private invariant obj != null;

    private Object obj = new Object();

    public void test(ILinkedList2 list1, ILinkedList2 list2) {
        list2.insert(obj);
    }
}