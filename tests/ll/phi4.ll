define i64 @main() {
entry: 
  br label %loop_top

loop_top:
  %iv = phi i64 [0, %entry], [%iv.next, %loop_top]
  %x = phi i64 [0, %entry], [%y, %loop_top]
  %y = phi i64  [0, %entry], [%iv.next, %loop_top]

  %iv.next = add i64 %iv, 1
  %b = icmp eq i64 %iv.next, 2
  br i1 %b, label %exit, label %loop_top

exit:
  ret i64 %x
}  
