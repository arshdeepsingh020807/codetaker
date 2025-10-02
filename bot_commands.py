# Additional bot commands to add to app.py after the existing /voucher command

@bot.on(events.NewMessage(pattern=r"^/balance (\w+)$"))
async def balance_handler(event):
    if event.sender_id != TELEGRAM_ADMIN_ID:
        return
    username = event.pattern_match.group(1)
    db = SessionLocal()
    user = db.query(User).filter(User.username == username).first()
    if not user:
        await event.reply("❌ User not found")
    else:
        await event.reply(f"👤 {user.username}\n💰 Credits: {user.credits}")
    db.close()

@bot.on(events.NewMessage(pattern=r"^/revoke (\w+)$"))
async def revoke_handler(event):
    if event.sender_id != TELEGRAM_ADMIN_ID:
        return
    code = event.pattern_match.group(1)
    db = SessionLocal()
    voucher = db.query(Voucher).filter(Voucher.code == code).first()
    if not voucher:
        await event.reply("❌ Voucher not found")
    else:
        voucher.redeemed = True
        db.commit()
        await event.reply(f"🛑 Voucher {code} revoked.")
    db.close()