#' Likelihood Ratio Test for Mixture of One- and Two-Sided Alternatives
#'
#' Performs a likelihood ratio test (LRT) to testing equality of means
#' across multiple groups against a mixture of one- and two-sided alternatives.
#' The test compares the null hypothesis of equal means for all groups
#' to the alternative that some follow one-sided (μ₀ ≤ μᵢ) and others two-sided
#' (μ₀ ≠ μⱼ) comparisons with the control.
#'
#' @param sample_data A list of numeric vectors. The first element represents
#'   the control group, the next \code{r} elements correspond to one-sided
#'   alternatives, and the remaining correspond to two-sided ones.
#' @param significance_level A numeric value between 0 and 1 specifying the
#'   significance level (e.g., \code{0.05}).
#' @param r Integer specifying the number of one-sided alternatives.
#' @param n.boot Number of bootstrap replications (default = \code{100000}).
#' @param seed Optional random seed for reproducibility.
#'
#' @return A character string containing the bootstrap critical value,
#'   observed LRT statistic, bootstrap p-value, and test decision.
#'
#' @details
#' The test evaluates:
#' \deqn{H_0: μ_0 = μ_i, \, i = 1, …, k \quad vs. \quad
#'       H_1: μ_0 ≤ μ_s \text{ for } s = 1, …, r
#'       \text{ or } μ_0 ≠ μ_t \text{ for } t = r+1, …, k}
#'
#' The LRT statistic is based on the ratio of maximized likelihoods
#' under the null and the mixture of one- and two-sided constraints.
#' Critical values and p-values are computed via a parametric bootstrap.
#'
#' @importFrom stats quantile rnorm var
#' @importFrom Iso pava
#' @export
#'
#'
#' @examples
#' set.seed(456)
#' control <- rnorm(20, mean = 5)
#' trt1 <- rnorm(25, mean = 6)
#' trt2 <- rnorm(22, mean = 7)
#' trt3 <- rnorm(18, mean = 4)
#' data_list <- list(control, trt1, trt2, trt3)
#' LRT(data_list, 0.05, r = 1, n.boot = 1000)
#' \donttest{
#' # Recommended: Use 100000 for research-level accuracy
#' LRT(data_list, 0.05, r = 1, n.boot = 100000)
#' }
LRT <- function(sample_data, significance_level, r, n.boot = 100000, seed = NULL) {
  R_MLE <- function(X, n) {
    X1 <- X[-1]
    n1 <- n[-1]
    sorted_indices <- order(X1)
    X1_sorted <- X1[sorted_indices]
    n1_sorted <- n1[sorted_indices]
    if (length(X)==2){
      if (all(X1 < X[1])){
        new_X <- c((X[1]*n[1]+X[2]*n[2])/sum(n),(X[1]*n[1]+X[2]*n[2])/sum(n))
      }
      else{
        new_X <- X
      }
      return(new_X)
    }
    else {
      A <- numeric(length(X1_sorted))
      for (j in 2:length(X)) {
        A[j-1] <- (n[1] * X[1] + sum(n1_sorted[1:(j - 1)] * X1_sorted[1:(j - 1)])) /
          (n[1] + sum(n1_sorted[1:(j - 1)]))
      }
      if (all(X1 >= X[1])) {
        new_X <- X
      } else if (A[length(X)-2] >= X1_sorted[length(X)-1]) {
        X <- rep(A[length(X)-1], length(X))
        new_X <- X
      } else {
        comparisons <- logical(length(X1_sorted) - 1)
        comparisons1 <- logical(length(X1_sorted) - 1)
        stored_values <- numeric(0)
        for (k in 1:(length(X1_sorted) - 1)) {
          comparisons[k] <- A[k] < X1_sorted[k + 1]
          if(comparisons1[k] <- A[k] < X1_sorted[k + 1]) {
            for (s in 1:k) {
              stored_values[s] <- X1_sorted[s]
            }
            break
          }
        }
        selected_A_values <- A[comparisons]
        X[1] <- selected_A_values[1]
        for (l in 2:length(X)) {
          if (X[l] %in% stored_values) {
            X[l] <- selected_A_values[1]
          }
        }
        new_X <- X
      }
      return(new_X)
    }
  }
  LRT_H0_new <- function(sample_data_list) {
    means <- sapply(sample_data_list, mean)
    sample_sizes <- sapply(sample_data_list, length)
    S <- unlist(sample_data_list)
    mu1 <- mean(S)
    var1 <- sapply(1:length(sample_data_list), function(i) sum((sample_data_list[[i]] - means[i])^2) / sample_sizes[i])
    u1 <- sample_sizes / var1

    repeat {
      new_mu1 <- (sum(u1 * means)) / sum(u1)
      new_var1 <- sapply(1:length(sample_data_list), function(i) sum((sample_data_list[[i]] - new_mu1)^2) / sample_sizes[i])
      new_u1 <- sample_sizes / new_var1

      if (max(abs(new_mu1 - mu1)) <= 0.0000001) {
        u1 <- new_u1
        mu1 <- new_mu1
        var1 <- new_var1
        break  # Exit the loop if the difference is less than epsilon
      }

      u1 <- new_u1
      mu1 <- new_mu1
      var1 <- new_var1
    }

    return(var1)
  }
  LRT_H1_new <- function(sample_data_list) {
    n <- sapply(sample_data_list, length)
    mu0 <- sapply(sample_data_list, mean)
    var0 <- sapply(1:length(sample_data_list), function(i) sum((sample_data_list[[i]] - mu0[i])^2) / n[[i]])
    w0 <- n / var0
    repeat {
      new_mu0 <- R_MLE(sapply(sample_data_list, mean), w0)
      new_var0 <- sapply(1:length(sample_data_list), function(i) sum((sample_data_list[[i]] - new_mu0[i])^2) / n[[i]])
      new_w0 <- n/new_var0

      if (max(abs(new_mu0 - mu0)) <= 0.0000001) {
        w0 <- new_w0
        mu0 <- new_mu0
        var0 <- new_var0
        break  # Exit the loop if the difference is less than epsilon
      }

      w0 <- new_w0
      mu0 <- new_mu0
      var0 <- new_var0
    }

    return(var0)
  }
  LRT_mixed <- function(sample_data_list, l){
    mean_all <- sapply(sample_data_list, mean)
    n_all <- sapply(sample_data_list, length)
    var_all <- sapply(1:length(sample_data_list), function(i) sum((sample_data_list[[i]] - mean_all[i])^2) / n_all[[i]])
    sample_data_part1 <- sample_data_list[1:(l+1)]
    LRT_H1_new_part1 <- LRT_H1_new(sample_data_part1)
    LRT_H1_new_part2 <- var_all[(l+2):length(sample_data_list)]
    LRT_stat_mixed <- c(LRT_H1_new_part1, LRT_H1_new_part2)
    if (l==0){
      return(var_all)
    } else if (l==(length(sample_data_list)-1)){
      return(LRT_H1_new(sample_data_list))
    } else {
      return(LRT_stat_mixed)
    }
  }

  if (!is.null(seed)) {
    set.seed(seed)
  }
  sample_data <- lapply(sample_data, function(x) x[!is.na(x)])
  num_samples <- n.boot
  num_datasets <- length(sample_data)
  n <- sapply(sample_data, length)
  lambda_values_star <- numeric(num_samples)

  # Bootstrap under null hypothesis
  for (i in 1:num_samples) {
    bootstrap_samples <- lapply(sample_data, function(x)
      rnorm(n = length(x), mean = 0, sd = sqrt(var(x))))
    V_R_star <- LRT_mixed(bootstrap_samples, r) / LRT_H0_new(bootstrap_samples)
    weights <- sapply(1:num_datasets, function(j)
      V_R_star[j]^(length(bootstrap_samples[[j]]) / 2))
    lambda_values_star[i] <- prod(weights)
  }

  # Critical value and test statistic
  quantile_value <- quantile(lambda_values_star, probs = significance_level)
  V_R <- LRT_mixed(sample_data, r) / LRT_H0_new(sample_data)
  weights <- sapply(1:num_datasets, function(i) V_R[i]^(length(sample_data[[i]]) / 2))
  lambda <- prod(weights)

  # Bootstrap-based p-value
  p_value <- mean(lambda_values_star <= lambda)

  # Decision
  if (lambda < quantile_value) {
    result <- "Reject null hypothesis"
  } else {
    result <- "Do not reject null hypothesis"
  }

  # Output
  return(paste(
    "Critical value:", quantile_value,
    "; LRT statistic:", lambda,
    "; p-value:", p_value,
    "; Result:", result
  ))
}


#' Maximum Difference-based Test for Mixture of One- and Two-Sided Alternatives
#'
#' Implements the \eqn{T_m} test, a maximum standardized mean-difference test
#' for testing equality of means across multiple groups against a mixture
#' of one- and two-sided alternative hypotheses. The test compares the null
#' hypothesis of equal means across all groups against the alternative that
#' some groups follow one-sided (\eqn{μ_0 ≤ μ_i}) and others follow two-sided
#' (\eqn{μ_0  ≠  μ_j}) comparisons with the control.
#'
#' @param sample_data A list of numeric vectors. The first element represents
#'   the control group, the next \code{r} elements correspond to one-sided
#'   alternatives, and the remaining correspond to two-sided ones.
#' @param significance_level A numeric value between 0 and 1 specifying the
#'   significance level (e.g., \code{0.05}).
#' @param r Integer specifying the number of one-sided alternatives.
#' @param n.boot Number of bootstrap replications to estimate the critical
#'   value (default = \code{100000}).
#' @param seed Optional random seed for reproducibility.
#'
#' @return A character string containing the bootstrap critical value,
#'   observed T_m statistic, bootstrap p-value, and test decision.
#'
#' @details
#' The hypotheses are defined as:
#' \deqn{
#' H_0: μ_0 = μ_i, \; i = 1, …, k
#' \quad \text{versus} \quad
#' H_1: μ_0 ≤ μ_s \text{ for } s = 1, …, r
#' \text{ or } μ_0  ≠  μ_t \text{ for } t = r+1, …, k.
#' }
#'
#' The test statistic is the maximum of standardized mean differences between
#' the control and treatment groups, computed separately for one-sided and
#' two-sided comparisons. Critical values and p-values are obtained via
#' a parametric bootstrap procedure using group-specific variances.
#'
#' @importFrom stats quantile rnorm var
#' @export
#'
#'
#' @examples
#' set.seed(456)
#' control <- rnorm(20, mean = 5)
#' trt1 <- rnorm(25, mean = 6)
#' trt2 <- rnorm(22, mean = 7)
#' trt3 <- rnorm(18, mean = 4)
#' data_list <- list(control, trt1, trt2, trt3)
#'
#' # Run test with fewer bootstrap replications for illustration
#' T_m(data_list, 0.05, r = 1, n.boot = 1000)
#'
#' \donttest{
#' # Recommended: Use 100000 for accurate inference
#' T_m(data_list, 0.05, r = 1, n.boot = 100000)
#' }
T_m <- function(sample_data, significance_level, r, n.boot = 100000, seed = NULL) {
  if (!is.null(seed)) { set.seed(seed) }

  sample_data <- lapply(sample_data, function(x) x[!is.na(x)])
  num_samples <- n.boot
  num_datasets <- length(sample_data)
  n <- sapply(sample_data, length)
  group_sds <- sapply(sample_data, function(x) sqrt(var(x)))
  T_max <- numeric(num_samples)

  for (u in 1:num_samples) {
    bootstrap_samples <- vector("list", num_datasets)   # Corrected initialization
    for (j in 1:num_datasets) {
      bootstrap_samples[[j]] <- rnorm(n = n[j], mean = 0, sd = group_sds[j])
    }
    D_star_max1 <- max(
      sapply(2:(r+1), function(i) {
        (mean(bootstrap_samples[[i]]) - mean(bootstrap_samples[[1]])) /
          sqrt(
            (var(bootstrap_samples[[i]]) / length(bootstrap_samples[[i]])) +
              (var(bootstrap_samples[[1]]) / length(bootstrap_samples[[1]])))
      }))


    D_star_max2 <-max(
      sapply((r+2):num_datasets, function(i) {
        (abs(mean(bootstrap_samples[[i]]) - mean(bootstrap_samples[[1]]))) /
          sqrt(
            (var(bootstrap_samples[[i]]) / length(bootstrap_samples[[i]])) +
              (var(bootstrap_samples[[1]]) / length(bootstrap_samples[[1]])))
      }))

    T_max[u] <- max(D_star_max1,D_star_max2)
  }

  Dm_values1 <- max(
    sapply(2:(r+1), function(i) {
      (mean(sample_data[[i]]) - mean(sample_data[[1]])) /
        sqrt(
          (var(sample_data[[i]]) / length(sample_data[[i]])) +
            (var(sample_data[[1]]) / length(sample_data[[1]])))
    }))

  Dm_values2 <- max(sapply((r+2):num_datasets, function(i) {
    (abs(mean(sample_data[[i]]) - mean(sample_data[[1]]))) /
      sqrt(
        (var(sample_data[[i]]) / length(sample_data[[i]])) +
          (var(sample_data[[1]]) / length(sample_data[[1]])))
  }))

  Tm_values <- max(Dm_values1,Dm_values2)

  quantile_value <- quantile(T_max, probs = 1 - significance_level, na.rm = TRUE)
  p_value <- mean(T_max >= Tm_values, na.rm = TRUE)

  # Decision
  if (Tm_values > quantile_value) { result <- "Reject null hypothesis" }
  else { result <- "Do not reject null hypothesis" }

  # Output summary
  return(paste(
    "Critical value:", quantile_value,
    "; T_m Test statistic:", Tm_values,
    "; p-value:", p_value,
    "; Result:", result
  ))
}




#' Min–Max Difference-based Test for Mixture of One- and Two-Sided Alternatives
#'
#' Implements the \eqn{T_{mm}} test, a hybrid statistic based on the
#' minimum of two maximum standardized mean-differences, for testing
#' equality of means across multiple groups against a mixture of one- and
#' two-sided alternative hypotheses. The test compares the null hypothesis
#' of equal means across all groups against the alternative that some
#' follow one-sided (\eqn{μ_0 ≤ μ_i}) and others two-sided (\eqn{μ_0  ≠  μ_j})
#' comparisons with the control.
#'
#' @param sample_data A list of numeric vectors. The first element represents
#'   the control group, the next \code{r} elements correspond to one-sided
#'   alternatives, and the remaining correspond to two-sided ones.
#' @param significance_level A numeric value between 0 and 1 specifying the
#'   significance level (e.g., \code{0.05}).
#' @param r Integer specifying the number of one-sided alternatives.
#' @param n.boot Number of bootstrap replications to estimate the critical
#'   value (default = \code{100000}).
#' @param seed Optional random seed for reproducibility.
#'
#' @return A character string containing the bootstrap critical value,
#'   observed T_mm statistic, bootstrap p-value, and test decision.
#'
#' @details
#' The hypotheses are defined as:
#' \deqn{
#' H_0: μ_0 = μ_i, \; i = 1, …, k
#' \quad \text{versus} \quad
#' H_1: μ_0 ≤ μ_s \text{ for } s = 1, …, r
#' \text{ or } μ_0  ≠  μ_t \text{ for } t = r+1, …, k.
#' }
#'
#' The test statistic \eqn{T_{mm}} is constructed as follows:
#' \itemize{
#'   \item For one-sided alternatives (\eqn{s = 1, …, r}), compute the maximum standardized mean difference between the control and these groups.
#'   \item For two-sided alternatives (\eqn{t = r+1, …, k}), compute the maximum absolute standardized mean difference.
#'   \item The overall statistic is the minimum of these two maxima.}
#'
#' Critical values and p-values are obtained through a parametric bootstrap
#' procedure based on group-specific variances.
#'
#' @importFrom stats quantile rnorm var
#' @export
#'
#' @examples
#' set.seed(456)
#' control <- rnorm(20, mean = 5)
#' trt1 <- rnorm(25, mean = 6)
#' trt2 <- rnorm(22, mean = 7)
#' trt3 <- rnorm(18, mean = 4)
#' data_list <- list(control, trt1, trt2, trt3)
#'
#' # Run test with fewer bootstrap replications for illustration
#' T_mm(data_list, 0.05, r = 1, n.boot = 1000)
#'
#' \donttest{
#' # Recommended: Use 100000 for accurate inference
#' T_mm(data_list, 0.05, r = 1, n.boot = 100000)
#' }
T_mm <- function(sample_data, significance_level, r, n.boot = 100000, seed = NULL) {
  if (!is.null(seed)) { set.seed(seed) }

  sample_data <- lapply(sample_data, function(x) x[!is.na(x)])
  num_samples <- n.boot
  num_datasets <- length(sample_data)
  n <- sapply(sample_data, length)
  group_sds <- sapply(sample_data, function(x) sqrt(var(x)))
  T_min <- numeric(num_samples)

  for (u in 1:num_samples) {
    bootstrap_samples <- vector("list", num_datasets)   # Corrected initialization
    for (j in 1:num_datasets) {
      bootstrap_samples[[j]] <- rnorm(n = n[j], mean = 0, sd = group_sds[j])
    }
    D_star_max1 <- max(
      sapply(2:(r+1), function(i) {
        (mean(bootstrap_samples[[i]]) - mean(bootstrap_samples[[1]])) /
          sqrt(
            (var(bootstrap_samples[[i]]) / length(bootstrap_samples[[i]])) +
              (var(bootstrap_samples[[1]]) / length(bootstrap_samples[[1]])))
      }))


    D_star_max2 <-max(
      sapply((r+2):num_datasets, function(i) {
        (abs(mean(bootstrap_samples[[i]]) - mean(bootstrap_samples[[1]]))) /
          sqrt(
            (var(bootstrap_samples[[i]]) / length(bootstrap_samples[[i]])) +
              (var(bootstrap_samples[[1]]) / length(bootstrap_samples[[1]])))
      }))

    T_min[u] <- min(D_star_max1,D_star_max2)
  }
  Dm_values1 <- max(
    sapply(2:(r+1), function(i) {
      (mean(sample_data[[i]]) - mean(sample_data[[1]])) /
        sqrt(
          (var(sample_data[[i]]) / length(sample_data[[i]])) +
            (var(sample_data[[1]]) / length(sample_data[[1]])))
    }))

  Dm_values2 <- max(sapply((r+2):num_datasets, function(i) {
    (abs(mean(sample_data[[i]]) - mean(sample_data[[1]]))) /
      sqrt(
        (var(sample_data[[i]]) / length(sample_data[[i]])) +
          (var(sample_data[[1]]) / length(sample_data[[1]])))
  }))

  Tmm_values <- min(Dm_values1,Dm_values2)

  quantile_value <- quantile(T_min, probs = 1 - significance_level, na.rm = TRUE)
  p_value <- mean(T_min >= Tmm_values, na.rm = TRUE)

  # Decision
  if (Tmm_values > quantile_value) { result <- "Reject null hypothesis" }
  else { result <- "Do not reject null hypothesis" }

  # Output summary
  return(paste(
    "Critical value:", quantile_value,
    "; T_mm Test statistic:", Tmm_values,
    "; p-value:", p_value,
    "; Result:", result
  ))
}


