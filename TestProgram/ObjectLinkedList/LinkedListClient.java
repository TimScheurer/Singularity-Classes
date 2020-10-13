package ObjectLinkedList;

public class LinkedListClient implements ILinkedListClient {
 
    //@ private invariant obj != null;

    private Object obj = new Object();

    public void test(ILinkedList list1, ILinkedList list2) {
        list2.insert(new Object());
    }
}