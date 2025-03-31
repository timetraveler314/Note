#import "@local/MetaNote:0.0.2" : *

#let detm = math.mat.with(delim: "|")

// #set text(font:("Charter", "FZShuSong-Z01"), lang: "cn")

#show: doc => MetaNote(
  title: [
    Operating Systems (Honor Track)
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

= Scheduling

== Concepts and Classic Policies

=== Scheduling Policy Goal/Criteria

Without any a priori knowledge of the workload, we cannot design a scheduling algorithm that is optimal for all possible workloads. Instead, we can only aim to design algorithms that are optimal for certain classes of workloads. Hence different criteria are used to evaluate the performance of scheduling algorithms.

- *Minimize Completion Time*: The time from the submission of a job to the time of its completion.