use serenity::{
    prelude::*,
    model::prelude::*,
    Client,
};
use std::{io, fs};
use std::io::Read;
use serde::Deserialize;

const CONFIG_FILE_PATH: &'static str = "../config.toml";

#[derive(Debug, Deserialize)]
struct Config {
    discord_bot_token: String,
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
}

struct Handler;
impl EventHandler for Handler {
    fn message(&self, context: Context, msg: Message) {
        if msg.content == "!ping" {
            if let Err(why) = msg.channel_id.say(&context.http, "pong!") {
                println!("Error sending message: {}", why);
            }
        }
    }
}

pub fn start() -> io::Result<()> {
    let config = Config::load()?;
    let mut client = Client::new(config.token(), Handler)?;
    client.start();
    Ok( () )
}