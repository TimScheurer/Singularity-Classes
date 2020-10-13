package ObjectLinkedList;

public interface ILinkedListClient2 {
        
    /*@ public normal_behaviour
      @ requires list1 != list2;
      @ requires list1 != null && list2 != null;
      @ requires \invariant_for(list2);
      @ requires list1.get(0) != null;
      @ ensures list1.get(0) == \old(list1).get(0);
      @*/
      public void test(ILinkedList2 list1, ILinkedList2 list2);
}