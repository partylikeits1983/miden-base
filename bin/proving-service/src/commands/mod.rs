use clap::Parser;
use proxy::StartProxy;
use tracing::instrument;
use update_workers::{AddWorkers, RemoveWorkers, UpdateWorkers};
use worker::{ProverType, StartWorker};

use crate::utils::MIDEN_PROVING_SERVICE;

pub mod proxy;
pub mod update_workers;
pub mod worker;

#[derive(Debug, Parser)]
pub(crate) struct ProxyConfig {
    /// Interval in milliseconds at which the system polls for available workers to assign new
    /// tasks.
    #[clap(long, default_value = "20", env = "MPS_AVAILABLE_WORKERS_POLLING_INTERVAL_MS")]
    pub(crate) available_workers_polling_interval_ms: u64,
    /// Maximum time in seconds to establish a connection.
    #[clap(long, default_value = "10", env = "MPS_CONNECTION_TIMEOUT_SECS")]
    pub(crate) connection_timeout_secs: u64,
    /// Health check interval in seconds.
    #[clap(long, default_value = "10", env = "MPS_HEALTH_CHECK_INTERVAL_SECS")]
    pub(crate) health_check_interval_secs: u64,
    /// Host of the proxy.
    #[clap(long, default_value = "0.0.0.0", env = "MPS_HOST")]
    pub(crate) host: String,
    /// Maximum number of items in the queue.
    #[clap(long, default_value = "10", env = "MPS_MAX_QUEUE_ITEMS")]
    pub(crate) max_queue_items: usize,
    /// Maximum number of requests per second per IP address.
    #[clap(long, default_value = "5", env = "MPS_MAX_REQ_PER_SEC")]
    pub(crate) max_req_per_sec: isize,
    /// Maximum number of retries per request.
    #[clap(long, default_value = "1", env = "MPS_MAX_RETRIES_PER_REQUEST")]
    pub(crate) max_retries_per_request: usize,
    /// Metrics configurations.
    #[clap(flatten)]
    pub(crate) metrics_config: MetricsConfig,
    /// Port of the proxy.
    #[clap(long, default_value = "8082", env = "MPS_PORT")]
    pub(crate) port: u16,
    /// Maximum time in seconds allowed for a request to complete. Once exceeded, the request is
    /// aborted.
    #[clap(long, default_value = "100", env = "MPS_TIMEOUT_SECS")]
    pub(crate) timeout_secs: u64,
    /// Worker update service port.
    ///
    /// Port used to add and remove workers from the proxy.
    #[clap(long, default_value = "8083", env = "MPS_WORKERS_UPDATE_PORT")]
    pub(crate) workers_update_port: u16,
    /// Supported prover type.
    ///
    /// The type of proof the proxy will handle. Only workers that support the same prover type
    /// will be able to connect to the proxy.
    #[clap(long, default_value = "transaction", env = "MPS_PROVER_TYPE")]
    pub(crate) prover_type: ProverType,
    /// Status port.
    ///
    /// Port used to get the status of the proxy. It is used to get the list of workers and their
    /// statuses, as well as the supported prover type and version of the proxy.
    #[clap(long, default_value = "8084", env = "MPS_STATUS_PORT")]
    pub(crate) status_port: u16,
}

#[derive(Debug, Parser)]
pub(crate) struct MetricsConfig {
    /// Enable metrics.
    #[clap(long, default_value = "false", env = "MPS_ENABLE_METRICS")]
    pub(crate) enable_metrics: bool,
    /// Prometheus metrics host.
    #[clap(long, default_value = "0.0.0.0", env = "MPS_PROMETHEUS_HOST")]
    pub(crate) prometheus_host: String,
    /// Prometheus metrics port.
    #[clap(long, default_value = "9090", env = "MPS_PROMETHEUS_PORT")]
    pub(crate) prometheus_port: u16,
}

/// Root CLI struct
#[derive(Parser, Debug)]
#[clap(
    name = "miden-proving-service",
    about = "A stand-alone service for proving Miden transactions.",
    version,
    rename_all = "kebab-case"
)]
pub struct Cli {
    #[clap(subcommand)]
    action: Command,
}

/// CLI actions
#[derive(Debug, Parser)]
pub enum Command {
    /// Starts the workers with the configuration defined in the command.
    StartWorker(StartWorker),
    /// Starts the proxy.
    StartProxy(StartProxy),
    /// Adds workers to the proxy.
    ///
    /// This command will make a request to the proxy to add the specified workers.
    AddWorkers(AddWorkers),
    /// Removes workers from the proxy.
    ///
    /// This command will make a request to the proxy to remove the specified workers.
    RemoveWorkers(RemoveWorkers),
}

/// CLI entry point
impl Cli {
    #[instrument(target = MIDEN_PROVING_SERVICE, name = "cli:execute", skip_all, ret(level = "info"), err)]
    pub async fn execute(&self) -> Result<(), String> {
        match &self.action {
            // For the `StartWorker` command, we need to create a new runtime and run the worker
            Command::StartWorker(worker_init) => worker_init.execute().await,
            Command::StartProxy(proxy_init) => proxy_init.execute().await,
            Command::AddWorkers(update_workers) => {
                let update_workers: UpdateWorkers = update_workers.clone().into();
                update_workers.execute().await
            },
            Command::RemoveWorkers(update_workers) => {
                let update_workers: UpdateWorkers = update_workers.clone().into();
                update_workers.execute().await
            },
        }
    }
}
