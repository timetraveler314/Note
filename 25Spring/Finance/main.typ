#import "@local/MetaNote:0.0.2" : *
#import "@preview/physica:0.9.0" : *

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    Introduction to Finance
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

#let balsheet = table.with(
  columns: 3, 
  align: center, 
  stroke: (x, y) => (if y == 0 { (bottom: 0.7pt + black) } else if x == 0 { (right: 0.7pt + black) }),
  table.header(
    [*Assets*],
    [*Liabilities*],
    [*Equity*]
  ), 
)

= Lec 3. Asset Classes

== Equities

Common Stock

- Ownership in a company
- Voting rights at shareholder meetings, residual claim on assets
- Dividends are not guaranteed

$
  "Market Value" = "Number of Shares" times "Price per Share"
$

== Derivatives

=== Option

#definition(title: "Option")[
  *Call Option* gives the holder the right to buy an asset at a specified(exerciesd/strike) price on or before a specified expiration date.

  *Put Option* gives the holder ...

  Option confers a *right*, not an *obligation*.
]

#definition(title: "Future")[

]

= Lec. 4 Trading, Margin and Short Sale

== How Firms Issue Security

=== Primary Market: New Issues of Stocks(Bonds)

- Public vs. Private Corporations: The requirement of public disclosure, and liquidity of shares.

- *Initial Public Offerings (IPOs)*: the first issue of stocks to the public, where bulks of IPO's go to Institutional Investors. Investment bankers determine suitable prices, identify potential buyers, and (sometimes) commit to buy unsold shares.

- *Process of IPO*:
- Underwriter: a financial institution that helps the firm issue securities.
- Prospectus
- Road Show

+ *Secondary Market*: Trading of Outstanding Securities (Securities already issued)

Organized secondary markets give assets liquidity.

== How Securities are Traded

=== Types of Markets

- Direct Search: buyers and sellers search for each other.
- Brokered Markets: brokers search for buyers and sellers. (e.g. the primary market)
- Dealer Markets: dealers have inventories of assets from which they buy and sell.
- Auction Markets: all traders converge at one place to buy or sell.

=== Bid and Ask Prices

- The market maintains a limit order book:
- *Bid*: highest price at which someone is willing to buy;
- *Ask*: lowest ... sell
- *Spread*: difference between bid and ask. Ask must be higher than bid, otherwise the deal is done immediately.

=== Orders

#definition(title: "Market Order")[
  buy/sell at the best available price.

  - Only quantity is specified, execution is immediate.
  - Posted ask price may change before the order is executed or as a result of the order.
]

#note(title: "Potential Problems with Market Orders")[
  - Large Orders: may not be executed at the same price.
  - Other Traders: another trader can beat our investor to the punch. Our order gets executed at a higher price.
  - Sudden Price Changes: the price at which the order is executed may be different from the price at which the order was placed.
]

#definition(title: "Limit Order")[
  buy/sell specified quantity at a specified price. 
  
  - Limit order is one kind of the _price-contingent order_ (the other being the stop order).
  - All limit orders are stored in the limit order book, which serves as a source of bid and ask prices.
]

== Margin Trading

#definition(title: "Buying on Margin")[
  borrowing money to buy securities.

  - *Debt-financed asset purchases*: some money put up by the investor, the rest borrowed from the broker.
  - *Broker's Call*: the broker can make a margin call if the value of the account falls below a certain level.
  - Shares are used as _collateral_ for the loan.
  - There is *Margin Requirement*: the minimum portion of the purchase price contributed by the investor.
]

#definition(title: "Margin Requirements")[
  - *Initial Margin*: the minimum margin that must be supplied at the time of purchase, usually 50%.
  - *Maintenance Margin*: applies subsequently, sensitive to the value of the account.

  If price drop so far that the margin requirement is not met, the broker will issue a margin call.
]

Before giving an example on margin trading, we need to understand the *balance sheet* of a margin account.

#theorem(title: "Equity in a Margin Account")[
  $
    "Assets" = "Liabilities" + "Equity"
  $
]

// #show table.cell.where(y: 0): strong
// #set table(
//     stroke: (x, y) => (if y == 0 {
//       (bottom: 0.7pt + black)
//     } else if x == 0 {
//       (right: 0.7pt + black)
//     }),
//     align: (x, y) => (
//       if x > 0 { center }
//       else { left }
//     )
//   )

#example(title: "Margin Trading Example")[
  Investor balance sheet (initially):

  Suppose an investor buys 100 shares of a stock at \$50 per share, with an initial margin of 50%. The stock pays no dividends. The maintenance margin is 30%.

  - *Initial Investment*: \$2500
  - *Loan*: \$2500
  - *Total Investment*: \$5000

  If the stock price falls to \$40, the investor's equity is \$1500, which is below the maintenance margin of \$1200. The broker will issue a margin call.

  The investor can either deposit more money or sell some shares to meet the margin requirement.
]

=== Short Sales (Selling Short)

*Purpose*: profit from a decline in the price of a security.

*Mechanism*: borrow shares from a broker, sell them and deposit proceeds and margin in an account (avoiding the risk of default); buy them back later to return to the broker (covering the short position).

= Lec. 5 Stock Market Indices

== Stock Market Indices

- *Index*: a measure of the value (average price) of a subset of the market (a collection of stocks).
- Types of Indices: 
  - *Price-Weighted (PWI)*: calculates the average price without weighting;
  - *Value-Weighted (VWI)*: weights the average price by the market value of the stocks, giving more weight to firms with higher market capitalization.

== Stock Splits

- *Purpose*: to reduce the price of a stock, making it more affordable to small investors.
- *No effect* on market capitalization or VWI.
- *PWIs* must be adjusted to reflect the split, just adjust the denominator to maintain the index value.

= Lec. 6 Funds

- Funds may be _open-ended_ or _closed-ended_.

== Open-Ended Funds (e.g. Mutual Funds, Hedge Funds)

- *Net Asset Value (NAV)*: the value of an investment fund.
  - $"NAV" = ("Assets" - "Liabilities") / "Number of Shares"$

- *Shares created and redeemed* by the fund based on the NAV: no secondary market, investors purchase or sell shares directly from the fund at NAV determined at the end of the trading day.

== Closed-Ended Funds (CEFs)

- *Definiton*: CEFs invest in a portfolio of assets and issue a fixed number of shares to the public. Shares are traded on the secondary market, or _trade on an exchange_.
  - CEFs raise capital through an IPO, then the portfolio manager invests the proceeds in a diversified portfolio of assets.
  - CEFs may issue additional shares through a secondary offering (uncommon though).
  - Shares are _not redeemable_ by the fund, but exit through the secondary market.
- *Market Price* of a CEF may differ from its NAV, due to supply and demand.
  - *Discount*: $"Price" < "NAV"$, *Premium*: $"Price" > "NAV"$.
  - $"Premium" = ("Price" - "NAV") / "NAV"$.
  - *Discount/Premium* is a measure of the market's confidence in the fund's ability to outperform the market.
  - *Arbitrage*: if the discount is too large, an investor can buy shares at a discount and sell them at NAV.

=== Arbitrage in CEFs

It is possible to make a profit by exploiting the difference between the market price and the NAV of a CEF.

- *Active approach*: force management to *liquidate* the fund and distribute the proceeds to shareholders, which an arbitrageur could do by acquiring a large stake in the fund.
  - Liquidation would force the fund's price to converge to its NAV.
  - *Risk*: the liquidation may not be profitable: liquidation may incur substantial costs. ...
- *Passive approach*: buy shares and hedge the asset risk.
  - *Illiquidity*: shorting all the assets in the fund may be difficult.
  - _Alternative approach_: purchase a diversified portfolio of CEFs trading at a discount, and hedge by shorting a broad stock index. ?

== Investor Migration to Index Funds and ETFs

=== Index Funds

- *Passively managed*: no attempt to outperform the market.
  - In contrast, actively managed funds try to beat the market with a portfolio manager picking securities.
  - Resulting in its *advantages*: low fees, ensure benchmark returns.

=== Exchange-Traded Funds (ETFs)

- ETFs combine characteristics of open-ended and closed-ended funds.
  - *Open-ended*: can redeem before the fund maturity;
  - *Closed-ended*: can trade freely on the exchange.


= Lec. 8 Historical Returns on Risky Portfolios

= Lec. 9 Introduction to Portfolio Return

== Risk and Risk Aversion

- Most investors are risk-averse: Informally, they prefer less risk to more risk for a given level of return.

Formally, we can construct a utility function to model attitudes toward risk. A simple model is:

$
  U = E(r) - 1/2 A sigma^2,
$

where $A$ is the coeff. of the investor's risk aversion, $E(r)$ is the expected return, and $sigma^2$ is the variance of the return.

= Lec 10. Constructing Portfolios

== Sharpe Ratio and Capital Allocation Line

#definition(title: "Sharpe Ratio")[
  The *Sharpe Ratio* (Reward-to-Votality Ratio) is a measure of the risk-adjusted return of an investment (i.e. the return in excess of the risk-free rate per unit of risk).

  $
    "Sharpe Ratio" = "Risk premium" / "SD of excess return" = (E(r_p) - r_f) / sigma_p,
  $

  where $E(r)$ is the expected return, $R_f$ is the risk-free rate, and $sigma$ is the standard deviation of the return.
]

Using the Sharpe Ratio, we can construct the *Capital Allocation Line (CAL)*, which is a graph representing the risk-return trade-off of a portfolio.

The portfolio return of a portfolio $C$ consisting of a risk-free asset and a risky asset (weight $y$) is:

$
  E(r_c) = r_f + y (E(r_p) - r_f) = r_f + S sigma_c,
$

which is linear in the standard deviation of the portfolio.

= Lec. 13 Index Models

$
  max_bold(w) U(bold(w)), "where" U(bold(w)) = (1 - bold(w)^top bold(1)) r_f + bold(w)^top bold(E(r)) - 1/2 A bold(w)^top bold(Sigma) bold(w)
$

Taking derivative w.r.t. $bold(w)$

$
  derivative(U(bold(w)),bold(w)) = r_f + underbrace(bold(w)^top (bold(E(r)) - bold(1) r_f)) - A bold(Sigma) bold(w) = 0
$
