.syntax unified
.cpu cortex-m0
.thumb
.text
.global sync_fixture
.type sync_fixture,%function
.thumb_func
sync_fixture:
  dmb sy
  dsb sy
  isb sy
  cpsid i
  cpsie i
  bx lr
.size sync_fixture, .-sync_fixture
