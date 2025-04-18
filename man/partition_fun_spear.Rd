% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/MSmix_functions_package.R
\name{partition_fun_spear}
\alias{partition_fun_spear}
\title{Partition function of the Mallows model with Spearman distance}
\usage{
partition_fun_spear(theta, n_items, log = TRUE)
}
\arguments{
\item{theta}{Non-negative precision parameter.}

\item{n_items}{Number of items.}

\item{log}{Logical: whether the partition function must be returned on the log scale. Defaults to \code{TRUE}.}
}
\value{
Either the exact or the approximate (log-)partition function of the Mallows model with Spearman distance.
}
\description{
Compute (either the exact or the approximate) (log-)partition function of the Mallows model with Spearman distance.
}
\details{
When \eqn{n\leq 20}, the partition function is exactly computed by relying on the Spearman distance distribution provided by OEIS Foundation Inc. (2023). When \eqn{n>20}, it is approximated with the method introduced by Crispino et al. (2023) and, if \eqn{n>170}, the approximation is also restricted over a fixed grid of values for the Spearman distance to limit computational burden.

The partition function is independent of the consensus ranking of the Mallows model with Spearman distance due to the right-invariance of the metric. When \eqn{\theta=0}, the partition function is equivalent to \eqn{n!}, which is the normalizing constant of the uniform (null) model.
}
\examples{

## Example 1. Partition function of the uniform (null) model, coinciding with n!.
partition_fun_spear(theta = 0, n_items = 10, log = FALSE)
factorial(10)

## Example 2. Partition function of the Mallows model with Spearman distance.
partition_fun_spear(theta = 0.5, n_items = 10, log = FALSE)

## Example 3. Log-partition function of the Mallows model with Spearman distance
## as a function of theta.
partition_fun_spear_vec <- Vectorize(partition_fun_spear, vectorize.args = "theta")
curve(partition_fun_spear_vec(x, n_items = 10), from = 0, to = 0.1, lwd = 2,
  xlab = expression(theta), ylab = expression(log(Z(theta))),
  main = "Log-partition function of the Mallows model with Spearman distance",
  ylim = c(7, log(factorial(10))))

## Example 4. Log-partition function of the Mallows model with Spearman distance
## for varying number of items and values of the concentration parameter.
partition_fun_spear_vec <- Vectorize(partition_fun_spear, vectorize.args = "theta")
curve(partition_fun_spear_vec(x, n_items = 10),
  from = 0, to = 0.1, lwd = 2, col = 2,
  xlab = expression(theta), ylab = expression(log(Z(theta))),
  main = "Log-partition function of the Mallows model with Spearman distance",
  ylim = c(0, log(factorial(30))))
curve(partition_fun_spear_vec(x, n_items = 20), add = TRUE, col = 3, lwd = 2)
curve(partition_fun_spear_vec(x, n_items = 30), add = TRUE, col = 4, lwd = 2)
legend("topright", legend = c(expression(n == 10), expression(n == 20), expression(n == 30)),
  col = 2:4, lwd = 2, bty = "n")

}
\references{
Crispino M, Mollica C, Astuti V and Tardella L (2023). Efficient and accurate inference for mixtures of Mallows models with Spearman distance. \emph{Statistics and Computing}, \bold{33}(98), DOI: 10.1007/s11222-023-10266-8.

OEIS Foundation Inc. (2023). The On-Line Encyclopedia of Integer Sequences, Published electronically at \url{https://oeis.org}.
}
\seealso{
\code{\link{spear_dist_distr}}, \code{\link{expected_spear_dist}}
}
