---
date: 2026-01-10
tags: [blockchain]
---

# Understanding Bitcoin: A Top-Down Approach

> [!TIP] 
> This article reflects my personal notes and may not resonate with everyone. In fact, I suspect most readers won't find it appealing—it's simply the way that feels most natural for me to understand Bitcoin, even though many of my friends have found my approach unconventional.
>
> However, it is also possible someone find it is very helpful, because if someone try to organize the knowledge in a way differ from their own thinking pattern, it may cause they add some defensive descrition to prevent reader to understand how they think. Hence, I also share the converstion history with Gemini AI [here](https://gemini.google.com/share/52dfd8912f38).

> [!NOTE] Abstract
> Bitcoin is an interesting thing. Even though today we have many fancy concepts for blockchain, like smart contracts, ZK, PoS, etc., Bitcoin doesn't apply any of these. It seems this is due to security considerations, which makes Bitcoin like digital gold: old but stable, it also make Bitcoin very suitable for learning the fundamental concepts of blockchain. I personally also tend to learn those things that exist in the real world, rather than some theoretical concepts that may never be implemented.

Bitcoin is running on a peer-to-peer network. Hence, each node stored (almost) the same data, these data include:
- **All transactions ever happened**: start from 2009-01-03 when the genesis block was mined. It is stored in a data structure called blockchain.
- **Unspent Transaction Outputs (UTXOs)**: these are the outputs of transactions that have not been spent yet. They represent the amount of Bitcoin that a user can spend.
- **Mempool**: this is a collection of unconfirmed transactions that are waiting to be included in a block.
- **Network related data**: since it is a P2P network, each node also needs to store information about its peers, such as their IP addresses and port numbers.

## What is UTXOs?

A natural question is what is UTXOs? Why we need it? Unspent Transaction Outputs actually are another form of all transactions. UTXOs are a set of UTXO, each UTXO is contains:
- **Value**: the amount of Bitcoin that can be spent.
- **ScriptPubKey**: a locking script that defines the conditions under which the UTXO can be spent.

## What is Transaction?

A transaction is a data structure that represents the transfer of Bitcoin from one or more inputs to one or more outputs. Each transaction contains:
- **Inputs**: references to UTXOs that are being spent and unlocking scripts (**ScriptSig**) that satisfy the conditions defined in the corresponding ScriptPubKey.
- **Outputs**: new UTXOs that are created as a result of the transaction.

> Both concept of UTXOs and Transactions are anti intuitive, my first question is why not just use account balance like traditional banking system? The answer is that UTXO model has several advantages over account-based model.

Each UTXO can be assumed as a coin, the coin have a locking script (ScriptPubKey), to spend the coin, you need to provide an unlocking script (ScriptSig) that satisfies the locking script. The script system is stack-based language, it is not Turing complete for security considerations (e.g., to prevent infinite loops). If you want to express the coin that have value 1 BTC belong to user A, and now you want to transfer 0.3 BTC to user B.

The UTXO of user A can be represented as:
```
Value: 1 BTC,
ScriptPubKey: 
    OP_DUP 
    OP_HASH160 
    <PubKeyHash_A> 
    OP_EQUALVERIFY
    OP_CHECKSIG
```

If user A wants to transfer 0.3 BTC to user B, user A need to specify one input and two outputs in the transaction, the input include a reference to the UTXO and a ScriptSig that can unlock the UTXO.
```yaml
Inputs:
    - PreviousOutput: <TxID_of_UTXO_of_user_A>
      ScriptSig:
          <Input_Signature_A>
          <Input_PubKey_A>
```
The ScriptSig is used to show that user A has the right to spend the UTXO, the verification process is to concatenate the ScriptSig and ScriptPubKey, then execute the script. If the result is true, the UTXO can be spent. In this case, if we concatenate the ScriptSig and ScriptPubKey, we get:
```
    <Input_Signature_A>
    <Input_PubKey_A>
    OP_DUP 
    OP_HASH160 
    <PubKeyHash_A> 
    OP_EQUALVERIFY
    OP_CHECKSIG
```
now let's execute the script step by step:
1. Push `<Input_Signature_A>` onto the stack.
2. Push `<Input_PubKey_A>` onto the stack.
3. OP_DUP duplicates the top item on the stack (which is `<Input_PubKey_A>`). The stack now contains: `<Input_PubKey_A>`, `<Input_PubKey_A>`, `<Input_Signature_A>`.
4. OP_HASH160 hashes the top item on the stack (`<Input_PubKey_A>`) using SHA-256 followed by RIPEMD-160. The stack now contains: `<PubKeyHash_Input_A>`, `<Input_PubKey_A>`, `<Input_Signature_A>`.
5. Push `<PubKeyHash_A>` onto the stack. The stack now contains: `<PubKeyHash_A>`, `<PubKeyHash_Input_A>`, `<Input_PubKey_A>`, `<Input_Signature_A>`.
6. OP_EQUALVERIFY checks if the top two items on the stack are equal. If they are not equal, the script fails. If they are equal, both items are removed from the stack. Assuming `<PubKeyHash_Input_A>` equals `<PubKeyHash_A>`, the stack now contains: `<Input_PubKey_A>`, `<Input_Signature_A>`.
7. OP_CHECKSIG verifies the signature (`<Input_Signature_A>`) against the public key (`<Input_PubKey_A>`). If the signature is valid, it pushes `true` onto the stack; otherwise, it pushes `false`. Assuming the signature is valid, the stack now contains: `true`. Please note that the `<Input_Signature_A>` is generated by signing the entire transaction data (include other inputs and outputs) with the private key corresponding to `<Input_PubKey_A>`.

> [!IMPORTANT]
> The last step is the most critical one, it ensures the intergrity and authenticity of the transaction. If the signature verification fails, it means that the transaction has been tampered with or that the spender does not possess the private key corresponding to the public key, and thus the UTXO cannot be spent. The miner can also not modify the transaction data (e.g., change the output value) without invalidating the signature.

> [!NOTE]
> This a very interesting design, Bitcoin do not store some meta data to indicate who own how much BTC, instead, it use script system to define the ownership. This make Bitcoin very flexible, for example, we can create multi-signature wallet by using different ScriptPubKey. You can also create time-lock transaction by using OP_CHECKLOCKTIMEVERIFY opcode. I will discuss it later.

> [!WARNING]
> Another interesting points is `Input_Signature_A` is generated by signing the entire transaction data (include other inputs and outputs) with the private key corresponding to `Input_PubKey_A`, but the signature itself is also a part of the transaction data. To solve this circular dependency, breifly, when signing the transaction, the ScriptSig fields of all inputs are set to empty (or a placeholder), then the transaction is serialized and signed. However, there are some implementation details and optimizations involved, which cause the SegWit upgrade. I will discuss it later.

The outputs of the transaction will create two new UTXOs, one for user B with value 0.3 BTC, and another for user A with value 0.7 BTC (the change). Since the ownership of the UTXOs is defined by ScriptPubKey, the outputs should also manufacture the ScriptPubKey accordingly.
```yaml
Outputs:
    - Value: 0.3 BTC
        ScriptPubKey:
            OP_DUP 
            OP_HASH160 
            <PubKeyHash_B> 
            OP_EQUALVERIFY
            OP_CHECKSIG
    - Value: 0.7 BTC
        ScriptPubKey:
            OP_DUP 
            OP_HASH160 
            <PubKeyHash_A> 
            OP_EQUALVERIFY
            OP_CHECKSIG
```
In this example, we do not discuss mutiply inputs and mutiply outputs, but the concept is similar. The total value of inputs must be equal to or greater than the total value of outputs, if it is greater, the difference is considered as transaction fee and will be collected by miners (the way how miners collect transaction fee is also interesting, I will discuss it later). The sender need to provide unlocking scripts (ScriptSig) for each input to prove that they have the right to spend the UTXOs. The miner will verify the transaction by executing the concatenated ScriptSig and ScriptPubKey for each input. If all inputs are valid, the transaction is considered valid.

## Where is the Account?

You many notice that in the above example, there is no concept of account or balance. This is because Bitcoin uses UTXO model instead of account-based model. The UTXO is like a locked check, you can only spend it if you have the right to unlock it. Imagine you want to create an new "account", you just do everything offline: generate a new private key, derive the public key, then hash the public key to get the PubKeyHash. The PubKeyHash is like your "acount number", but because the account balance is zero, so the blockchain do not need to store anything for you. When someone want to send you some BTC, they will create a transaction with an output that has a ScriptPubKey containing your PubKeyHash. 

## How Transactions are Added to the Blockchain?

We just discussed how transactions work in principle, but how these transactions are added to the blockchain? This is where miners come in. Each miner is a node in the Bitcoin network, it maintains a mempool of unconfirmed transactions. 

If you want to send some BTC to someone, you need to create a transaction and broadcast it to the network. The transaction will be propagated to all nodes and be added to their mempool.

 Miners will select transactions from their mempool by **using their own strategy** (usually based on transaction fees). Each block can have multiple transactions, but the total size of the block must not exceed 4 MB (since SegWit upgrade).  A block contains the following fields:
- **Block Header**: contains metadata about the block, includes:
  - **Version**: 4 bits, indicates the version of the block.
  - **Previous Block Hash**: 32 bytes, the hash of the previous block in the blockchain, that is why it is called blockchain.
  - **Merkle Root**: 32 bytes, the root hash of the Merkle tree of all transactions included in the block.
  - **Timestamp**: 4 bytes, the time when the block was created.
  - **Difficulty Target**: 4 bytes, the target threshold for the block hash.
  - **Nonce**: 4 bytes, a counter used for the proof-of-work algorithm.
- **Block Body**: contains a list of transactions included in the block.
  - **Transaction Count**: a variable-length integer indicating the number of transactions in the block.
  - **Transactions**: a list of transactions included in the block.
    - **Coinbase Transaction**: a special transaction that rewards the miner for creating the block.
    - **Regular Transactions**: transactions selected from the mempool.
- **SegWit Data** (if applicable): contains witness data for SegWit transactions.

> [!NOTE]
> SegWit (Segregated Witness) is an upgrade to the Bitcoin protocol that separates the witness data (signatures) from the transaction data. It is also a very interesting concept, because it is hard to upgrade a running blockchain system in institution level. I will discuss it later.

When a miner want to create a new block, it will first select transactions from its mempool, then construct the block body. Next, it will create the block header, create the Merkle tree from the transactions to get the Merkle root, set the previous block hash to the hash of the latest block in the blockchain, set the timestamp to the current time, set the difficulty target based on the network difficulty, and start the proof-of-work process. 


### What is Merkle Tree ?
The merkle tree is a binary tree where each leaf node is the hash of a transaction, and each non-leaf node is the hash of the concatenation of its two child nodes. The Merkle root is the topmost node of the tree, it provides a compact representation of all transactions in the block and allows for efficient verification of transaction inclusion. For example, if we have four transactions: Tx1, Tx2, Tx3, and Tx4, the Merkle tree would be constructed as follows:
```
        Merkle Root
        /          \
   Hash12        Hash34
   /    \        /     \
Hash1  Hash2  Hash3   Hash4
```
If we add two more transactions in the new block: Tx5 and Tx6, the new Merkle tree would look like this:
```
            New Merkle Root
            /             \
    Old Merkle Root    New Hash56
      /      \         /      \
  Hash12    Hash34   Hash5    Hash6
  /   \       /   \  
Hash1 Hash2 Hash3 Hash4
```
As you can see, the old Merkle root is still part of the new Merkle tree, which means that all transactions in the previous block are still included in the new block. The structure of the Merkle tree allows for efficient verification of transaction inclusion, as only a small number of hashes need to be checked to verify that a transaction is included in the block.

### What is Proof-of-Work?

The proof-of-work process involves finding a nonce such that the hash of the block header is less than the difficulty target. The formula is:
$$
\text{Sha256}(\text{Sha256}(\text{BlockHeader})) < \text{DifficultyTarget}
$$
The miner will increment the nonce and recalculate the hash until it finds a valid nonce. Once a valid nonce is found, the miner will broadcast the new block to the network. Other nodes will verify the block by checking the proof-of-work, validating all transactions in the block, and ensuring that the block follows the consensus rules. If the block is valid, it will be added to the blockchain, and the miner will receive the block reward (newly minted Bitcoin) and transaction fees from all transactions included in the block.

### What is the structure of Coinbase Transaction?

Coinbase transaction is a special type of transaction that is created by miners to claim the block reward and transaction fees for mining a new block. It is the first transaction in a block and has no inputs. It does not have UTXO inputs, or we can assume that its input are all rest of the transactions in the block. The structure of a coinbase transaction includes:
- **Inputs**: contains a single input with a special script called the coinbase script.
- **Outputs**: contains one or more outputs that specify the amount of Bitcoin being rewarded to the miner and any transaction fees collected from other transactions in the block.

The reward amount have two parts:
1. **Block Reward**: this is the newly minted Bitcoin that is created with each block. The block reward started at 50 BTC in 2009 and halves approximately every four years (210,000 blocks). As of 2024, the block reward is 6.25 BTC, and it will halve to 3.125 BTC in 2024.
2. **Transaction Fees**: this is the total amount of transaction fees collected from all transactions included in the block. Each transaction can include a fee that is paid to the miner who includes it in the block.

As you can see, the transaction fee is defined by the sender of the transaction, and miners have the incentive to include transactions with higher fees in their blocks to maximize their rewards.

## Rethinking Point 1

At that point, I already know many basic concepts of Bitcoin, I also leave some contents for later discussion, like SegWit upgrade, how scripts can be used to create multi-signature wallets and time-lock transactions, etc. But before moving on, I want to rethink some questions to ensure I really understand these concepts.

#### Q1: If Miner decides which transactions to include in the block, it is possible every miner have different mempool, and thus create different blocks? How the network reach consensus in this case?
> A: Yes, it is possible that different miners have different mempools and thus create different blocks. However, the Bitcoin network uses a consensus mechanism called Nakamoto Consensus to ensure that all nodes agree on the state of the blockchain. When a miner creates a new block, it broadcasts the block to the network. Other nodes will verify the block and add it to their local copy of the blockchain if it is valid. If two miners create different blocks at the same time (a fork), nodes will temporarily have different versions of the blockchain. However, as more blocks are added to the chain, one branch will become longer than the other, and nodes will switch to the longest valid chain. This process ensures that all nodes eventually agree on a single version of the blockchain.
>
> On the other hand, find the valid nonce is a hard problem, every ten minutes on average only one miner can find the valid nonce, this make the forking event very rare. Hence, the network can almost always reach consensus. The answer can also used to exlpain how to prevent the evil miner to create invalid blocks, because the evil miner need to redo the proof-of-work for the invalid block, which is computationally expensive.

#### Q2: What if over 50% of the mining power is controlled by evil miners? Can they create invalid blocks and double spend?
> A: If over 50% of the mining power is controlled by evil miners, they can potentially create invalid blocks and double spend. This is known as a 51% attack. In such an attack, the evil miners can create a longer chain of blocks that includes their double-spent transactions. However, it may also make the price of Bitcoin drop significantly, which is not in the interest of the evil miners themselves. 
>
> These attacker owns a large portion of the mining power, they also have a significant investment in the Bitcoin network. If they attack the network and cause the price of Bitcoin to drop, they may suffer significant financial losses. Therefore, while a 51% attack is theoretically possible, it is not necessarily in the best interest of the attackers to carry it out.

#### Q3: If we create a isolated Bitcoin network, will it cause there are two different Bitcoin networks? How does it effect the price of Bitcoin?
> A: Yes, if we create an isolated Bitcoin network that is not connected to the main Bitcoin network, it will result in two separate Bitcoin networks. It is actually happened before, for example, Bitcoin Cash and Bitcoin SV are two separate networks that were created as a result of hard forks from the main Bitcoin network. Every user own 1 BTC in the main network will also own 1 BCH or 1 BSV in the new networks.

> ##### 1. Two Ways to Create a Network

> * **Scenario A: The "Clone" (Independent Network)**
If you take the Bitcoin source code and start a brand-new chain from scratch (a new "Genesis Block"), you have created a new cryptocurrency (like Litecoin).
> * **Effect:** It has **zero effect** on the original Bitcoin. It’s like printing your own "Monopoly" money; it doesn't make the US Dollar any less valuable.
> 
> 
> * **Scenario B: The "Hard Fork" (Shared History)**
> This happens when you take the existing Bitcoin ledger but change the rules moving forward. This is what happened with **Bitcoin Cash (BCH)** and **Bitcoin SV (BSV)**.
> * **The "Free Money" Effect:** Because the history is shared, anyone who held **1 BTC** on the original chain at the moment of the split suddenly finds they also own **1 BCH** on the new chain.
> 
> ##### 2. The Impact on Price: "Code is Cheap, Consensus is Expensive"
> 
> While you can easily copy the **code**, you cannot easily copy the **Social Consensus**. This is why the price of the original Bitcoin usually remains dominant:
> 
> * **Network Effects:** The value of Bitcoin comes from the millions of users, merchants, and developers using it. A new, isolated network starts with zero users, making its tokens worth very little.
> * **Security (Hash Power):** Miners follow the profit. Since the original Bitcoin has the highest price, it attracts the most computing power, making it the most secure. An isolated network with low hash power is vulnerable to **51% attacks**.
> * **Market Dilution:** In 2017, many feared that forks would dilute the 21-million-cap. However, the market quickly realized that "Bitcoin" is a brand tied to the most secure chain. The price of forks usually trends downward relative to BTC over time.

#### Q4. The creator of a transaction need to indicate the input UTXOs, but how they provide the information of UTXOs to the miner? Do they need provide the ID of UTXOs? If so, how the miner can find the UTXOs from the ID?
> A: Yes, the creator of a transaction needs to specify the input UTXOs by providing the transaction ID (TxID) and the output index of each UTXO being spent. The TxID is a unique identifier for each transaction, which is calculated by hashing the serialized transaction data. The output index indicates which output of the transaction is being spent (since a transaction can have multiple outputs).
>
> When a miner receives a transaction, it can look up the UTXOs in its local copy of the blockchain. Each node maintains a database of all UTXOs, which is updated whenever a new block is added to the blockchain. The miner can use the TxID and output index provided in the transaction to find the corresponding UTXO in its database. If the UTXO exists and is unspent, the miner can then verify the transaction by executing the unlocking script (ScriptSig) against the locking script (ScriptPubKey) of the UTXO.

#### Q5. How TxID stored in the Blockchain?
> The TxID is not explicitly stored in the blockchain; instead, it is derived from the transaction data itself. When a transaction is created, it is serialized into a byte format, and then a double SHA-256 hash of this serialized data is computed to produce the TxID. This means that the TxID is a unique fingerprint of the transaction.

#### Q6. What will happen if two different transactions have the same TxID?
> In 2012, two coinbase transactions were found to have the same TxID due to a bug in the Bitcoin software. One miner receive same reward to same address twice. This event is known as a [BIP-34](https://github.com/bitcoin/bips/blob/master/bip-0034.mediawiki). The Bitcoin network fix it by requiring that the block height be included in the coinbase transaction, which ensures that each coinbase transaction has a unique TxID.

## Who decides the difficulty target?

The difficulty target is adjusted every 2016 blocks (approximately every two weeks) to ensure that blocks are mined at an average rate of one block every 10 minutes. The adjustment is based on the time it took to mine the previous 2016 blocks. If the blocks were mined faster than the target time, the difficulty will increase; if they were mined slower, the difficulty will decrease. This mechanism ensures that the Bitcoin network maintains a consistent block time despite changes in the total mining power of the network.

But who controls it in a decentralized network? The answer is that it is controlled by the consensus rules of the Bitcoin protocol. All nodes in the network follow the same rules for adjusting the difficulty target, and miners must adhere to these rules when creating new blocks. If a miner attempts to create a block with an invalid easier or harder difficulty target, other nodes will reject the block. This ensures that the difficulty target is consistently applied across the entire network.

## How to write the custom locking script?

Although the script itself allow very flexible logic, in practice, most transactions use a few standard script templates for security and compatibility reasons. The non-standard scripts may not be relayed or mined by all nodes, which can lead to transaction delays or failures. The most common standard script types are:
- **Pay-to-PubKey-Hash (P2PKH)**: the most common type, which we discussed earlier.
- **Pay-to-Script-Hash (P2SH)**: allows for more complex scripts by hashing the script and using the hash in the ScriptPubKey.
- **Multi-Signature Scripts**: require multiple signatures to spend the UTXO, often used in P2SH or P2WSH.
- **Null Data (OP_RETURN)**: allows for storing arbitrary data in the blockchain, often used for non-financial purposes.
- **Witness （SegWit） Scripts**: used in SegWit transactions to separate witness data from transaction data.
  -  **Pay-to-Witness-PubKey-Hash (P2WPKH)**: used in SegWit transactions to separate witness data from transaction data.
  - **Pay-to-Witness-Script-Hash (P2WSH)**: similar to P2SH but used in SegWit transactions.
- **Pay-to-Taproot (P2TR)**: used in Taproot transactions, which is an upgrade that enhances privacy and flexibility.

If you want to create a custom locking script, you can use P2SH to bypass, let me use a example to illustrate how it works.
1. First, you need to write your custom script, for example, a multi-signature script that requires two out of three signatures to spend the UTXO.
```
OP_2
<PubKey1>
<PubKey2>
<PubKey3>
OP_3
OP_CHECKMULTISIG
```
2. Next, you need to hash the script using SHA-256 followed by RIPEMD-160 to get the script hash.
3. Then, you create a P2SH ScriptPubKey using the script hash.
```
OP_HASH160
<ScriptHash>
OP_EQUAL
```
4. When you want to spend the UTXO, you need to provide the original script and the required signatures in the ScriptSig.
```
<Empty>  # Due to a bug in OP_CHECKMULTISIG, an extra item is needed
<Signature1>
<Signature2>
<OriginalScript>
```
5. The miner will concatenate the ScriptSig and ScriptPubKey, then execute the script to verify the transaction.

## Bitcoin Upgrades

Currently, Bitcoin still have many shortcomings, the most notable one is scalability. The original design of Bitcoin can only handle about 7 transactions per second, which is far below the requirements of a global payment system. To address this issue, several upgrades have been proposed and implemented over the years, including:
- **Segregated Witness (SegWit)**: implemented in 2017, SegWit separates the witness data (signatures) from the transaction data, allowing for more transactions to fit in a block. It also fixes the transaction malleability issue, which is important for second-layer solutions like the Lightning Network.
- **Taproot**: implemented in 2021, Taproot enhances privacy and flexibility by allowing complex scripts to appear as simple transactions on the blockchain. It also improves the efficiency of multi-signature transactions.
- **Lightning Network**: a second-layer (L2) solution that enables fast and low-cost transactions by creating off-chain payment channels between users. It leverages the security of the Bitcoin blockchain while allowing for instant transactions.

Before moving on, I want to discuss why upgrade is possible in a decentralized network? Because it seems we need majority of the nodes to agree on the upgrade, otherwise, it may cause a hard fork.

Briefly, the upgraude happens through social and technical consensus, which meams everyone believe the upgrade is beneficial to the network. The upgrade process usually involves several steps:
1. **Proposal**: a Bitcoin Improvement Proposal (BIP) is created to outline the details of the upgrade.
2. **Discussion**: the proposal is discussed within the Bitcoin community, including developers, miners, and users.
3. **Implementation**: the upgrade is implemented in the Bitcoin software.
4. **Activation**: the upgrade is activated through a signaling mechanism, where miners signal their support for the upgrade by including a specific bit in the block header. Once a certain threshold of blocks signal support, the upgrade is activated.

To better understand the consensus mechanism, we can revise a famous battle which is "Block Size War". In 2017, there was a debate within the Bitcoin community about whether to increase the block size limit to improve scalability. Some members of the community believed that increasing the block size would allow for more transactions to be processed per block, while others argued that it would lead to centralization and security risks. To resolve this debate, a proposal called Segregated Witness (SegWit) was introduced, which not only increased the effective block size but also addressed transaction malleability issues. 

But big blockers were not satisfied with SegWit alone, they wanted a direct increase in the block size limit. This led to the creation of Bitcoin Cash (BCH) in August 2017, which implemented a larger block size limit of 8 MB. The split resulted in two separate cryptocurrencies: Bitcoin (BTC) and Bitcoin Cash (BCH). Some miners are also do not want to accept SegWit upgrade, then the User-Activated Soft Fork (UASF) mechanism was proposed, which allowed users to signal their support for the upgrade by running software that enforced the new rules. This put pressure on miners to adopt the upgrade, as they risked losing support from users if they did not comply. Eventually, the majority of miners adopted SegWit, and it was activated on the Bitcoin network in August 2017. This event proofs that
> Users, not miners, ultimately control the Bitcoin network.

## SegWit Upgrade

The SegWit upgrade is a significant improvement to the Bitcoin protocol. First, it resolves a critical vulnerability known as Quadratic Sighash Problem. Recall the Locking Script and Unlocking Script we discussed earlier, the last step is to verify the signature by using `OP_CHECKSIG` opcode. If we check the algiorithm of signature verification or generation, we will find its complexity is $O(n^2)$, where is the number of inputs. If an attacker create a transaction with many inputs, it will cause the signature verification to take a long time, which can be exploited to launch a denial-of-service (DoS) attack on the network. 

The original algorithm of signature generation and verification is as follows: A transaction have $n$ inputs, each input contains a ScriptSig and a reference to a UTXO, which means we need to geneate $n$ signatures for each input, each signature generation process be like:
1. Create a copy of the transaction.
2. For each input in the transaction copy, set the ScriptSig to an empty script (or a placeholder), except for the input being signed, which retains its original ScriptSig.
3. Serialize the modified transaction copy.
4. Hash the serialized transaction using SHA-256 twice to produce a message digest.
5. Use the private key corresponding to the public key in the ScriptSig to sign the message digest, producing the signature.
6. Insert the generated signature into the ScriptSig of the input being signed.

The pseudocode for the above algorithm is as follows:
```cpp
for (auto &input : transaction.inputs) {
    Transaction txCopy = transaction;
    for (auto& in : txCopy.inputs) {
        in.scriptSig = (in == input) ? in.scriptSig : EmptyScript;
    }
    uint8_t[] serializedTx = Serialize(txCopy);
    uint8_t[] messageDigest = SHA256(SHA256(serializedTx));
    uint8_t[] signature = Sign(messageDigest, input.privateKey);
    input.scriptSig.insert(signature);
}
```

As we can see, for each input, we need to serialize and hash the entire transaction, and format of transaction for each input is different, which means the total complexity is $O(n^2)$. To solve this problem, SegWit introduces a new way to calculate the signature hash (sighash) that separates the witness data (signatures) from the transaction data. The new algorithm is as follows:
1. Create a copy of the transaction.
2. For each input in the transaction copy, set the ScriptSig to an empty script (or a placeholder). (**different from the original algorithm**)
3. Serialize the modified transaction copy without the witness data.
4. Hash the serialized transaction using SHA-256 twice to produce a message digest.
5. Use the private key corresponding to the public key in the ScriptSig to sign the message digest, producing the signature.
6. Insert the generated signature into the witness data of the input being signed. (**different from the original algorithm**)

The pseudocode for the new algorithm is as follows:
```cpp
Transaction txCopy = transaction;
for (auto& in : txCopy.inputs) {
    in.scriptSig = EmptyScript; // Set all ScriptSigs to empty
}
uint8_t[] serializedTx = SerializeWithoutWitness(txCopy);
uint8_t[] messageDigest = SHA256(SHA256(serializedTx));
for (auto &input : transaction.inputs) {
    uint8_t[] signature = Sign(messageDigest, input.privateKey);
    transaction.witnessData.insert(signature);
}
```

By separating the witness data from the transaction data, SegWit allows for more efficient signature generation and verification, reducing the complexity to $O(n)$. 

**You may want to ask why we need to separate the witness data from the transaction data but not insert them into placeholder in ScriptSig?** The answer is because of *Transaction Malleability Attack* and *lightning network* (L2 solutions).

The speed of transaction of bitcoin is very slow because we generate a new block every 10 minutes, to improve the speed, someone propose the concept of L2 solutions, which means we can create a second layer on top of the Bitcoin blockchain to handle transactions off-chain, while still leveraging the security of the underlying blockchain. The most notable L2 solution is the Lightning Network. 

However, *Transaction Malleability Attack* is a critical issue that needs to be addressed before implementing L2 solutions. Transaction malleability refers to the ability to modify a transaction's ID (TxID) without changing its content. This can cause problems for L2 solutions, for example, considering following scenario of Exchange like Binance:
1. User A wants to deposit 1 BTC to Binance.
2. Binance provides User A with a deposit address and waits for the transaction to be confirmed on the Bitcoin blockchain.
3. User A creates a transaction to send 1 BTC to the deposit address.
4. An attacker intercepts the transaction and modifies it in a way that changes its TxID.
5. The modified transaction is confirmed on the Bitcoin blockchain, but Binance is still waiting for the original transaction with the original TxID.
6. User A's deposit is not recognized by Binance, leading to confusion and potential loss of funds.

You may want to ask why Binance do not ask the user to provide the confirmed transaction details? The answer is Binance can do it but it means the user need to wait much longer time which will cause the meaning of using L2 solution is lost. The another question is how the attacker can modify the transaction id without changing its content? I will discuss it in another article because most of them content is related to the cryptographic algorithm.

After fixing the two issues, blockchain can support L2 solutions like Lightning Network in principle. I will discuss its principle later.

## Taproot Upgrade

The main purpose of Taproot upgrade is to enhance privacy and flexibility of Bitcoin transactions. Originally, complex transactions, such as multi-signature transactions or those with time-lock conditions, were easily identifiable on the blockchain. For example, a multi-signature transaction would reveal the public keys involved and the number of required signatures. This transparency could potentially expose user behavior and transaction patterns.

To resolve this multi-signature transaction privacy issue, Taproot introduces Schnorr signatures ([BIP 340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki)), which allow multiple signatures to be aggregated into a single signature. This means that a multi-signature transaction can appear identical to a standard single-signature transaction on the blockchain, enhancing privacy. 
> [!NOTE]
> Of course, the signature algorithm is determined by the ScriptPubKey, so we need to create a new ScriptPubKey to support Schnorr signatures. The new ScriptPubKey is called Pay-to-Taproot (P2TR), which uses a new opcode `OP_CHECKSIGADD` ([BIP 342](https://github.com/bitcoin/bips/blob/master/bip-0342.mediawiki)) to verify Schnorr signatures.
>
> I have another question when I leaned the Schnorr signature, which is why the privacy is so important? The answer is because Bitcoin is pseudonymous, meaning that while transactions are public, the identities of the users behind those transactions are not directly linked to their Bitcoin addresses. However, with enough analysis, it is possible to link addresses to real-world identities, especially when users reuse addresses or interact with centralized services like exchanges. Enhancing privacy helps protect users from such analysis and potential targeting.

The another feature of Taproot is to allow complex scripts to be hidden unless they are needed. For example, if a UTXO can be spent by any one of conditions is met, these cnditions may be:
- A single signature from Alice.
- If Alice is unavailable for a certain period, then two signatures from Bob and Charlie.
- If the transaction is not spent within a certain time frame, then a signature from Dave.

Please note that all these conditions are represented as scripts, if we have 5 scripts, we can combine them into a Merkle tree, the Merkle tree can be represented as follows in any forms, here are some examples:
```
          Root                         Root          Root
         /    \                       /    \        /    \
     Hash12   Hash345          Hash1234    S5     S1    Hash2345
      /  \     /  \             /  \                     /  \
   S1    S2  S3   Hash45    Hash12  Hash34             S2   Hash345
                  /   \      /  \    /  \                   /   \
                S4     S5   S1  S2  S3  S4                 S3   Hash45
                                                                 /   \
                                                               S4     S5
```
Then we need to show what will happen if someone want to use condition S3 to spend the UTXO. The UTXO will only store a:
$$
P_{\text{tweaked}}=P_{\text{internal}}+H(P_{internal||Root})G
$$
it is a formula related to eclipse curve, to avoid to understand too many cryptographic concepts, we can care about how to use it. First, the UTXO only store `P_tweaked`, which is exactly same as a normal UTXO storing a public key. If some one want to spend the UTXO, there are two ways to do it.

#### Key Path Spending
Provide a signature of the transaction using the private key corresponding to `P_tweaked`. The signature may be a Schnorr signature of mutiple parties if `P_tweaked` is derived from multiple public keys.

> [!NOTE]
> You may confuse why the path even need to exist, our original plan is to use the UTXO when one of the scripts is satisfied, but now we can use the public key to spend it directly? It looks like we construct a backdoor to bypass all scripts. The answer is also privacy, such design we can make the UTXO exactly same as normal before we use it in Script Path Spending (will discuss later). However, if we hope to ban the Key Path Spending, we can provide a `P_internal` that no one know the corresponding private key, then the only way to spend the UTXO is through Script Path Spending.

#### Script Path Spending
Provide:
- $P_{\text{internal}}$
- The Merkle proof from the root to the script S3, which will be like follows if we use the first Merkle tree structure above:
```
        Root
        /  \
   Hash12  Hash345
            /   \
        S3    Hash45
```
As you can say, we only provide a subset of the Merkle tree, so that others even can not know the number of scripts in the Merkle tree. They can only infer that there are at least three scripts.

> [!NOTE]
> In practice, we can organize the tree in Huffman coding way to minimize the size of Merkle proof. For example, if S3 is used more frequently than S4 and S5, we can make S3 closer to the root.

Now the miner need to verify the spending request, it will first compute:
1. Compute $P_{\text{tweaked}}$ using the provided $P_{\text{internal}}$ and the Merkle root.
2. Verify the signature using $P_{\text{tweaked}}$.
3. Verify the provided script S3 by executing it with the transaction data.
4. Verify the Merkle proof to ensure that S3 is indeed part of the Merkle tree represented by the root.

## Rethinking Point 2

#### Q: In the Script Path Spending of Taproot, we may find we can remove the $P_{\text{internal}}$ and only keep the Merkle root in the UTXO, but why the design still keep $P_{\text{internal}}$?
> A: The reason to keep $P_{\text{internal}}$ is to allow for Key Path Spending, which provides an additional way to spend the UTXO. By including $P_{\text{internal}}$, the UTXO can be spent directly using a signature corresponding to $P_{\text{tweaked}}$, without needing to reveal any scripts or Merkle proofs. This enhances privacy, as the UTXO can appear identical to a standard single-signature transaction on the blockchain.
>
> To be honest, I am not very understand this part. I believe the main reason is I do not fully understand why such kind of privacy is important. I will try to learn more about it later. But it definitely make the design more elegant because it is compatible with the original UTXO design.

## Summary

In this article, I do not discuss the detail of:
- Proof of why concensus can be reached in a decentralized network, I tend to understand them through intuitive way.
- Details of Cryptographic algorithms, like ECDSA and Schnorr signature. Actually, I think most cryptographic algorithms follows the same "API" of RSA design, I do not need consider too much about the implementation of API. The API can have mutiply backends, but we also need to notice the difference of security level of different algorithms.
- Details of L2 solutions, like Lightning Network. I think it is better to discuss them when we use Ethereum, because Ethereum have more flexible smart contract design.
