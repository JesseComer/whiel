//! CLI entry for one symbolic task or a named benchmark campaign.

use std::process::ExitCode;

use whiel_runner::cli::{CliAction, USAGE, execute_cli, parse_cli_args};
use whiel_runner::{campaign_cli, certificate_cli};

fn main() -> ExitCode {
    let action = match parse_cli_args(std::env::args_os().skip(1)) {
        Ok(action) => action,
        Err(error) => {
            eprintln!("error: {error}\n\n{USAGE}");
            return ExitCode::from(1);
        }
    };
    match action {
        CliAction::Help => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        CliAction::CertificateHelp => {
            print!("{}", certificate_cli::CERTIFICATE_USAGE);
            ExitCode::SUCCESS
        }
        CliAction::CampaignHelp => {
            print!("{}", campaign_cli::CAMPAIGN_USAGE);
            ExitCode::SUCCESS
        }
        CliAction::CampaignRun(Ok(config)) => {
            match campaign_cli::execute_campaign_run_cli(*config, std::io::stdout().lock()) {
                Ok(code) => ExitCode::from(code as u8),
                Err(error) => {
                    eprintln!("error: {error}");
                    ExitCode::from(error.exit_code as u8)
                }
            }
        }
        CliAction::CampaignCertifyHelp => {
            print!("{}", campaign_cli::CAMPAIGN_CERTIFY_USAGE);
            ExitCode::SUCCESS
        }
        CliAction::CampaignCertify(Ok(config)) => {
            match campaign_cli::execute_campaign_certify_cli(*config, std::io::stdout().lock()) {
                Ok(code) => ExitCode::from(code as u8),
                Err(error) => {
                    eprintln!("error: {error}");
                    ExitCode::from(error.exit_code as u8)
                }
            }
        }
        CliAction::CampaignCertify(Err(error)) => {
            eprintln!("error: {error}\n\n{}", campaign_cli::CAMPAIGN_CERTIFY_USAGE);
            ExitCode::from(campaign_cli::CAMPAIGN_ARGUMENT_FAILURE as u8)
        }
        CliAction::CampaignRun(Err(error)) => {
            eprintln!("error: {error}\n\n{}", campaign_cli::CAMPAIGN_USAGE);
            ExitCode::from(campaign_cli::CAMPAIGN_ARGUMENT_FAILURE as u8)
        }
        CliAction::Run(config) => match execute_cli(*config, std::io::stdout().lock()) {
            Ok(code) => ExitCode::from(code as u8),
            Err(error) => {
                eprintln!("error: {error}");
                ExitCode::from(1)
            }
        },
        CliAction::CertificateBuild(Ok(config)) => {
            match whiel_runner::certificate_cli::execute_certificate_build_cli(
                *config,
                std::io::stdout().lock(),
            ) {
                Ok(code) => ExitCode::from(code as u8),
                Err(error) => {
                    eprintln!("error: {error}");
                    ExitCode::from(1)
                }
            }
        }
        CliAction::CertificateBuild(Err(error)) => {
            eprintln!("error: {error}\n\n{}", certificate_cli::CERTIFICATE_USAGE);
            ExitCode::from(2)
        }
    }
}
