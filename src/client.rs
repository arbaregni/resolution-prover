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
use crate::prover;
use serenity::utils::MessageBuilder;
use serenity::framework::standard::{HelpOptions, CommandGroup, help_commands};
use std::collections::HashSet;

const CONFIG_FILE_PATH: &'static str = "config.toml";

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
        println!("{} is connected!", ready.user.name);
    }
}

#[group]
#[commands(verify)]
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
#[description("attempts to prove the expression with no priors, reacting ✅ if a proof is found, ❌ otherwise.\nNOTE: this is not the same thing as being true or false.")]
fn verify(ctx: &mut Context, msg: &Message, args: Args) -> CommandResult {
    let givens = vec![];
    let goal = args.message();
    println!("servicing request for {}, sent at {}", msg.author.name, msg.timestamp);
    match prover::service_proof_request(givens.as_slice(), goal) {
        Ok(success) => {
            // react to the message depending on whether we were able to prove the goal
            let r = if success { PROVABLE_REACT } else { UNPROVABLE_REACT };
            msg.react(ctx, r)?;
        }
        Err(err) => {
            let why = err.to_string();
            let response = MessageBuilder::new()
                .push_bold("Error with verify command\n")
                .push(why.as_str())
                .build();
            if let Err(why) = msg.channel_id.say(&ctx.http, &response) {
                println!("error sending message: {:?}", why);
            }
        }
    }
    Ok( () )
}

pub fn start() -> Result<(), Box<(dyn std::error::Error + 'static)>> {
    let config = Config::load()?;
    let mut client = Client::new(config.token(), Handler)?;
    client.with_framework(StandardFramework::new()
        .configure(|c| c
            .prefix(config.prefix())
        )
        .help(&MY_HELP)
        .group(&GENERAL_GROUP)
    );
    client.start()?;
    Ok( () )
}