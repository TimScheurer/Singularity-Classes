package ObjectArrayList;

public interface IArrayListClient2 {

    /*@ public normal_behaviour
      @ requires list1 != list2;
      @ requires list1 != null && list2 != null;
      @ requires list2.theList.length < 16;
      @ requires \invariant_for(list2);
      @ requires list1.get(0) != null;
      @ ensures \old(list1).get(0) == list1.get(0);
      @*/
      public void modOne(IArrayList2 list1, IArrayList2 list2);
}