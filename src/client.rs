use serenity::{
    prelude::*,
    model::prelude::*,
    framework::standard::{
        CommandResult, Args, macros::{command, group, help},
    },
    Client,
};
use std::{io, fs};
use std::io::Read;
use serde::Deserialize;
use serenity::framework::StandardFramework;
use serenity::utils::MessageBuilder;
use serenity::framework::standard::{HelpOptions, CommandGroup, help_commands, DispatchError};
use std::collections::HashSet;
use crate::error::BoxedErrorTrait;

const CONFIG_FILE_PATH: &'static str = "config.toml";
const GITHUB_LINK: &'static str = "https://github.com/arbaregni/resolution-prover/";

const PROVABLE_REACT: char = '✅';
const UNPROVABLE_REACT: char = '❌';

#[derive(Debug, Deserialize)]
struct Config {
    discord_bot_token: String,
    prefix: String,
}
impl Config {
    pub fn load() -> io::Result<Config> {
        let mut file = fs::File::open(CONFIG_FILE_PATH)?;
        let mut buf = String::new();
        file.read_to_string(&mut buf)?;
        let config = toml::from_str(buf.as_str())?;
        Ok(config)
    }
    pub fn token(&self) -> &str { self.discord_bot_token.as_str() }
    pub fn prefix(&self) -> &str { self.prefix.as_str() }
}

struct Handler;
impl EventHandler for Handler {
    fn ready(&self, _: Context, ready: Ready) {
        info!("{} is connected!", ready.user.name);
    }
}

#[group]
#[commands(about, prove, clauses)]
struct General;

#[help]
#[max_levenshtein_distance(3)]
#[command_not_found_text = "Could not find: `{}`."]
fn my_help(
    context: &mut Context,
    msg: &Message,
    args: Args,
    help_options: &'static HelpOptions,
    groups: &[&'static CommandGroup],
    owners: HashSet<UserId>
) -> CommandResult {
    help_commands::with_embeds(context, msg, args, help_options, groups, owners)
}

#[command]
#[description("about this project")]
fn about(ctx: &mut Context, msg: &Message, _args: Args) -> CommandResult {
    msg.channel_id.send_message(&ctx.http, |m| {
        m.embed(|e| {
            e.title("click for source")
                .description(&format!("uses resolution to verify statements and proofs\nreacting means {} a proof is found, {} means no proof is found\n",
                                       PROVABLE_REACT, UNPROVABLE_REACT)
                )
                .url(GITHUB_LINK)
        })
    })?;
    Ok( () )
}

#[command]
#[bucket = "rate-limited"]
#[description("attempts to prove the expression")]
fn prove(ctx: &mut Context, msg: &Message, args: Args) -> CommandResult {
    let givens = vec![];
    let goal = args.message();
    match resolution_prover::find_proof(givens.as_slice(), goal) {
        Ok(success) => {
            // react to the message depending on whether we were able to prove the goal
            let r = if success { PROVABLE_REACT } else { UNPROVABLE_REACT };
            msg.react(ctx, r)?;
        }
        Err(err) => {
            let why = err.to_string();
            let response = MessageBuilder::new()
                .push_bold("Error with verify command\n")
                .push_codeblock_safe(why.as_str(), None)
                .build();
            msg.channel_id.say(&ctx.http, &response)?;
        }
    }
    Ok( () )
}
#[command]
#[description("converts an expression to clausal normal form")]
fn clauses(ctx: &mut Context, msg: &Message, args: Args) -> CommandResult {
    let query = args.message();
    match resolution_prover::find_clause_set(query) {
        Ok(clause_set) => {
            let content = format!("{:#?}", clause_set.clauses);
            msg.channel_id.say(&ctx.http, &content)?;
        }
        Err(err) => {
            let why = err.to_string();
            let content = MessageBuilder::new()
                .push_bold("Error with clauses command\n")
                .push_codeblock_safe(why.as_str(), None)
                .build();
            msg.channel_id.say(&ctx.http, &content)?;
        }
    }
    Ok( () )
}

pub fn start() -> std::result::Result<(), BoxedErrorTrait> {
    let config = Config::load()?;
    let mut client = Client::new(config.token(), Handler)?;
    client.with_framework(StandardFramework::new()
        .configure(|c| c
            .prefix(config.prefix())
        )
        .help(&MY_HELP)
        .before(|_, msg, cmd_name| {
            info!("running command `{}` for {}, sent at {}", cmd_name, msg.author.name, msg.timestamp);
            true
        })
        .after(|_, msg, cmd_name, error| {
           if let Err(why) = error {
               error!("error running command `{}` for {}, sent at {}: {:?}",
                      cmd_name, msg.author.name, msg.timestamp, why);
           }
        })
        .unrecognised_command(|ctx, msg, unknown_cmd| {
            let response = match unknown_cmd {
                "verify" => {
                    format!("Unknown command `verify`. Help: `verify` was recently renamed to `prove`")
                }
                _ => {
                    return;
                }
            };
            if let Err(e) = msg.channel_id.say(&ctx.http, response) {
                error!("error responding to unknown command: {}", e);
            }
        })
        // limit to once per seven seconds
        .bucket("rate-limited", |b| b.delay(7))
        .on_dispatch_error(|ctx, msg, error| {
            if let DispatchError::Ratelimited(seconds) = error {
                let _ = msg.channel_id.say(&ctx.http, &format!("Rate limited. Try again in {} seconds.", seconds));
            }
        })
        .group(&GENERAL_GROUP)
    );
    client.start()?;
    Ok( () )
}