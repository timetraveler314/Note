#import "@local/MetaNote:0.0.1" : *

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    Practice of Frontier Computing
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

=