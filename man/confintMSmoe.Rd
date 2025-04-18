% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/MSmix_functions_package.R
\name{confintMSmoe}
\alias{confintMSmoe}
\alias{print.confintMSmoe}
\title{Hessian-based confidence intervals for mixtures of Mallows models with Spearman distance}
\usage{
confintMSmoe(object, conf_level = 0.95)

\method{print}{confintMSmoe}(x, ...)
}
\arguments{
\item{object}{An object of class \code{"emMSmoe"} returned by \code{\link{fitMSmoe}}.}

\item{conf_level}{Value in the interval (0,1] indicating the desired confidence level of the interval estimates. Defaults to 0.95.}

\item{x}{An object of class \code{"confintMSmoe"} returned by \code{\link{confintMSmoe}}.}

\item{...}{Further arguments passed to or from other methods (not used).}
}
\value{
A list with the following named components:

\item{\code{ci_theta}}{The confidence intervals for the precision parameters.}
\item{\code{ci_weights}}{The confidence intervals for the mixture weights (when \eqn{G>1}), otherwise \code{NULL}.}
}
\description{
Return the Hessian-based confidence intervals of the continuous parameters of a mixture of Mallows models with Spearman distance fitted to full rankings, namely the component-specific precisions and weights.

\code{print} method for class \code{"confintMSmoe"}.
}
\details{
The current implementation of the hessian-based confidence intervals assumes that the observed rankings are complete.
}
\examples{

## Example 1. Simulate rankings from a 2-component mixture of Mallows models
## with Spearman distance.
set.seed(123)
d_sim <- rMSmix(sample_size = 75, n_items = 8, n_clust = 2)
rankings <- d_sim$samples
# Fit the basic Mallows model with Spearman distance.
set.seed(123)
fit1 <- fitMSmix(rankings = rankings, n_clust = 1, n_start = 10)
# Compute the hessian-based confidence intervals for the MLEs of the precision.
confintMSmix(object = fit1)
# Fit the true model.
set.seed(123)
fit2 <- fitMSmix(rankings = rankings, n_clust = 2, n_start = 10)
# Compute the hessian-based confidence intervals for the MLEs of the weights and precisions.
confintMSmix(object = fit2)

}
\references{
Crispino M, Mollica C and Modugno L (2025). MSmix: An R Package for clustering partial rankings via mixtures of Mallows Models with Spearman distance. \emph{(submitted)}

Marden JI (1995). Analyzing and modeling rank data. \emph{Monographs on Statistics and Applied Probability} (64). Chapman & Hall, ISSN: 0-412-99521-2. London.

McLachlan G and Peel D (2000). Finite Mixture Models. \emph{Wiley Series in Probability and Statistics}, John Wiley & Sons.
}
