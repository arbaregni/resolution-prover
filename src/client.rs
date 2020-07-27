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
use std::collections::{HashMap, HashSet};
use crate::error::BoxedErrorTrait;

const CONFIG_FILE_PATH: &'static str = "config.toml";
const GITHUB_LINK: &'static str = "https://github.com/arbaregni/resolution-prover/";

const PROVABLE_REACT: char = '✅';
const UNPROVABLE_REACT: char = '❌';

/// Up to how many characters we typically display of a longer message
const TEASER_LEN: usize = 12;

/// Used to format time stamps in the given storage
/// Currently, it is formatted as ctime: `Sun Jul  8 00:34:60 2001`
const DATETIME_FORMATTER: &'static str = "%c";


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
#[commands(about, givens, prove, clauses)]
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

type TimeStamp = chrono::DateTime<chrono::FixedOffset>;

/// Lookup key for Context::data
struct GivenEventStorage;

impl TypeMapKey for GivenEventStorage {
    // map the user who used the `givens` command to the message arguments
    type Value = HashMap<UserId, (String, TimeStamp)>;
}

fn update_givens(ctx: &mut Context, msg: &Message, source: String) -> Option<(String, TimeStamp)> {
    let mut data = ctx.data.write();
    let given_store = data.get_mut::<GivenEventStorage>().expect("missing given event storage");
    given_store.insert(msg.author.id, (source, msg.timestamp))
}

fn clear_givens(ctx: &mut Context, user_id: UserId) -> Option<(String, TimeStamp)> {
    let mut data = ctx.data.write();
    let given_store = data.get_mut::<GivenEventStorage>().expect("missing given event storage");
    // clear the store
    given_store.remove(&user_id)
}

fn retrieve_givens(ctx: &mut Context, user_id: UserId) -> (String, Option<TimeStamp>) {
    let mut data = ctx.data.write();
    let given_store = data.get_mut::<GivenEventStorage>().expect("missing given event storage");
    match given_store.get(&user_id) {
        None => (String::new(), None),
        Some((source, ts)) => (source.clone(), Some(ts.clone())),
    }
}

#[command]
#[description("the next prove command you send will assume your current list of givens.\nCalling `givens` with no arguments clears your store.")]
fn givens(ctx: &mut Context, msg: &Message, args: Args) -> CommandResult {
    let response = if args.message().trim().is_empty() {
        // an empty givens means clear the store
        let prev = clear_givens(ctx, msg.author.id);
        let what_happened_to_the_old_givens = if let Some((prev_source, prev_ts)) = prev {
            let (teaser, _) = prev_source.split_at(TEASER_LEN);
            format!(", forgetting the old ones which were set at {} and began with `{}...`",
                    prev_ts.format(DATETIME_FORMATTER), teaser)
        } else {
            format!("")
        };
        format!("Cleared givens for {}{}", msg.author.name, what_happened_to_the_old_givens)
    } else {
        // associate the arguments with the author of the message
        let prev = update_givens(ctx, msg, args.message().to_string());
        let what_happened_to_the_old_givens = if let Some((prev_source, prev_ts)) = prev {
            let (teaser, _) = prev_source.split_at(TEASER_LEN);
            format!(", replacing the old ones which were set at {} and began with `{}...`",
                    prev_ts.format(DATETIME_FORMATTER), teaser)
        } else {
            format!("")
        };
        format!("Set givens for {}{}", msg.author.name, what_happened_to_the_old_givens)
    };
    msg.channel_id.say(&ctx.http, response)?;

    Ok( () )
}

#[command]
#[bucket = "rate-limited"]
#[description("attempts to prove the expression")]
fn prove(ctx: &mut Context, msg: &Message, args: Args) -> CommandResult {
    let (given_source, opt_ts) = retrieve_givens(ctx, msg.author.id);
    let givens = given_source.as_str().lines().collect::<Vec<&str>>();
    let goal= args.message();
    match resolution_prover::find_proof(givens.as_slice(), goal) {
        Ok(success) => {
            // react to the message depending on whether we were able to prove the goal
            let r = if success { PROVABLE_REACT } else { UNPROVABLE_REACT };
            msg.react(&ctx.http, r)?;
            // if we used a given set, say what the timestamp of it was
            if let Some(ts) = opt_ts {
                let response = format!("(used given set defined by {} at {})", msg.author.name, ts.format(DATETIME_FORMATTER));
                msg.channel_id.say(&ctx.http, &response)?;
            }
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
            .delimiters(vec!['\n','\r'])
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

    {
        let mut data = client.data.write();
        data.insert::<GivenEventStorage>(HashMap::new());
    }


    client.start()?;
    Ok( () )
}