#import "@local/MetaNote:0.0.1" : *

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    Introduction to Computer Systems
  ],
  authors: (
    (
      name: "timetraveler314",
      affiliation: "University of Genshin",
      email: "timetraveler314@outlook.com",
    ),
  ),
  doc,
)

= 程序的机器级表示

== 访问信息

#example[
  ```yasm
  movb $0xF, (%ebx) // 错误，%ebx 不能作为内存寄存器
  ```
]