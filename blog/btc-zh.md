---
date: 2026-01-10
tags: [blockchain]
---

# 理解比特币：自顶向下的方法
# Understanding Bitcoin: A Top-Down Approach

> [!TIP]
> This article reflects my personal notes and may not resonate with everyone. In fact, I suspect most readers won't find it appealing—it's simply the way that feels most natural for me to understand Bitcoin, even though many of my friends have found my approach unconventional.
>
> However, it is also possible someone find it is very helpful, because if someone try to organize the knowledge in a way differ from their own thinking pattern, it may cause they add some defensive descrition to prevent reader to understand how they think. Hence, I also share the converstion history with Gemini AI [here](https://gemini.google.com/share/52dfd8912f38).

> [!TIP] 提示
> 这篇文章反映了我的个人笔记，可能不适合所有人。事实上，我认为大多数读者不会觉得它有吸引力——这只是我理解比特币最自然的方式，尽管我的许多朋友认为我的方法不太常规。
>
> 然而，也有可能有人会发现它非常有帮助，因为如果有人试图以不同于他们自己思维模式的方式组织知识，可能会导致他们添加一些防御性描述来防止读者理解他们的想法。因此，我也在[这里](https://gemini.google.com/share/52dfd8912f38)分享了与 Gemini AI 的对话历史。

> [!NOTE] Abstract
> Bitcoin is an interesting thing. Even though today we have many fancy concepts for blockchain, like smart contracts, ZK, PoS, etc., Bitcoin doesn't apply any of these. It seems this is due to security considerations, which makes Bitcoin like digital gold: old but stable, it also make Bitcoin very suitable for learning the fundamental concepts of blockchain. I personally also tend to learn those things that exist in the real world, rather than some theoretical concepts that may never be implemented.

> [!NOTE] 摘要
> 比特币是一个有趣的东西。尽管今天我们有许多关于区块链的新奇概念，如智能合约、ZK、PoS 等，但比特币并不应用这些。这似乎是出于安全考虑，这使得比特币就像数字黄金：古老但稳定，这也使得比特币非常适合学习区块链的基本概念。我个人也倾向于学习那些存在于现实世界中的东西，而不是一些可能永远不会被实现的理论概念。

---

Bitcoin is running on a peer-to-peer network. Hence, each node stored (almost) the same data, these data include:

比特币运行在点对点网络上。因此，每个节点存储（几乎）相同的数据，这些数据包括：

- **All transactions ever happened**: start from 2009-01-03 when the genesis block was mined. It is stored in a data structure called blockchain.

  **所有发生过的交易**：从 2009-01-03 创世区块被挖出时开始。它存储在一个叫做区块链的数据结构中。

- **Unspent Transaction Outputs (UTXOs)**: these are the outputs of transactions that have not been spent yet. They represent the amount of Bitcoin that a user can spend.

  **未花费交易输出（UTXOs）**：这些是尚未被花费的交易输出。它们代表用户可以花费的比特币数量。

- **Mempool**: this is a collection of unconfirmed transactions that are waiting to be included in a block.

  **内存池（Mempool）**：这是等待被包含在区块中的未确认交易的集合。

- **Network related data**: since it is a P2P network, each node also needs to store information about its peers, such as their IP addresses and port numbers.

  **网络相关数据**：由于它是一个 P2P 网络，每个节点还需要存储关于其对等节点的信息，如它们的 IP 地址和端口号。

## What is UTXOs?
## 什么是 UTXOs？

A natural question is what is UTXOs? Why we need it? Unspent Transaction Outputs actually are another form of all transactions. UTXOs are a set of UTXO, each UTXO is contains:

一个自然的问题是什么是 UTXOs？为什么我们需要它？未花费交易输出实际上是所有交易的另一种形式。UTXOs 是一组 UTXO，每个 UTXO 包含：

- **Value**: the amount of Bitcoin that can be spent.

  **价值**：可以花费的比特币数量。

- **ScriptPubKey**: a locking script that defines the conditions under which the UTXO can be spent.

  **ScriptPubKey（锁定脚本）**：定义 UTXO 可以被花费的条件的锁定脚本。

## What is Transaction?
## 什么是交易？

A transaction is a data structure that represents the transfer of Bitcoin from one or more inputs to one or more outputs. Each transaction contains:

交易是一种数据结构，表示比特币从一个或多个输入转移到一个或多个输出。每个交易包含：

- **Inputs**: references to UTXOs that are being spent and unlocking scripts (**ScriptSig**) that satisfy the conditions defined in the corresponding ScriptPubKey.

  **输入**：对正在被花费的 UTXOs 的引用和解锁脚本（**ScriptSig**），这些脚本满足相应 ScriptPubKey 中定义的条件。

- **Outputs**: new UTXOs that are created as a result of the transaction.

  **输出**：作为交易结果创建的新 UTXOs。

> Both concept of UTXOs and Transactions are anti intuitive, my first question is why not just use account balance like traditional banking system? The answer is that UTXO model has several advantages over account-based model.

> UTXOs 和交易的概念都是反直觉的，我的第一个问题是为什么不像传统银行系统那样使用账户余额？答案是 UTXO 模型相比基于账户的模型有几个优势。

---

Each UTXO can be assumed as a coin, the coin have a locking script (ScriptPubKey), to spend the coin, you need to provide an unlocking script (ScriptSig) that satisfies the locking script. The script system is stack-based language, it is not Turing complete for security considerations (e.g., to prevent infinite loops). If you want to express the coin that have value 1 BTC belong to user A, and now you want to transfer 0.3 BTC to user B.

每个 UTXO 可以被假定为一个硬币，硬币有一个锁定脚本（ScriptPubKey），要花费这个硬币，你需要提供一个满足锁定脚本的解锁脚本（ScriptSig）。脚本系统是基于栈的语言，出于安全考虑，它不是图灵完备的（例如，防止无限循环）。如果你想表达一个价值 1 BTC 的硬币属于用户 A，现在你想转移 0.3 BTC 给用户 B。

The UTXO of user A can be represented as:

用户 A 的 UTXO 可以表示为：

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

如果用户 A 想要转移 0.3 BTC 给用户 B，用户 A 需要在交易中指定一个输入和两个输出，输入包括对 UTXO 的引用和可以解锁 UTXO 的 ScriptSig。

```yaml
Inputs:
    - PreviousOutput: <TxID_of_UTXO_of_user_A>
      ScriptSig:
          <Input_Signature_A>
          <Input_PubKey_A>
```

The ScriptSig is used to show that user A has the right to spend the UTXO, the verification process is to concatenate the ScriptSig and ScriptPubKey, then execute the script. If the result is true, the UTXO can be spent. In this case, if we concatenate the ScriptSig and ScriptPubKey, we get:

ScriptSig 用于证明用户 A 有权花费 UTXO，验证过程是连接 ScriptSig 和 ScriptPubKey，然后执行脚本。如果结果为真，则可以花费 UTXO。在这种情况下，如果我们连接 ScriptSig 和 ScriptPubKey，我们得到：

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

现在让我们逐步执行脚本：

1. Push `<Input_Signature_A>` onto the stack.
   将 `<Input_Signature_A>` 压入栈。

2. Push `<Input_PubKey_A>` onto the stack.
   将 `<Input_PubKey_A>` 压入栈。

3. OP_DUP duplicates the top item on the stack (which is `<Input_PubKey_A>`). The stack now contains: `<Input_PubKey_A>`, `<Input_PubKey_A>`, `<Input_Signature_A>`.
   OP_DUP 复制栈顶的项（即 `<Input_PubKey_A>`）。栈现在包含：`<Input_PubKey_A>`、`<Input_PubKey_A>`、`<Input_Signature_A>`。

4. OP_HASH160 hashes the top item on the stack (`<Input_PubKey_A>`) using SHA-256 followed by RIPEMD-160. The stack now contains: `<PubKeyHash_Input_A>`, `<Input_PubKey_A>`, `<Input_Signature_A>`.
   OP_HASH160 使用 SHA-256 然后 RIPEMD-160 对栈顶的项（`<Input_PubKey_A>`）进行哈希。栈现在包含：`<PubKeyHash_Input_A>`、`<Input_PubKey_A>`、`<Input_Signature_A>`。

5. Push `<PubKeyHash_A>` onto the stack. The stack now contains: `<PubKeyHash_A>`, `<PubKeyHash_Input_A>`, `<Input_PubKey_A>`, `<Input_Signature_A>`.
   将 `<PubKeyHash_A>` 压入栈。栈现在包含：`<PubKeyHash_A>`、`<PubKeyHash_Input_A>`、`<Input_PubKey_A>`、`<Input_Signature_A>`。

6. OP_EQUALVERIFY checks if the top two items on the stack are equal. If they are not equal, the script fails. If they are equal, both items are removed from the stack. Assuming `<PubKeyHash_Input_A>` equals `<PubKeyHash_A>`, the stack now contains: `<Input_PubKey_A>`, `<Input_Signature_A>`.
   OP_EQUALVERIFY 检查栈顶的两项是否相等。如果不相等，脚本失败。如果相等，两项都从栈中移除。假设 `<PubKeyHash_Input_A>` 等于 `<PubKeyHash_A>`，栈现在包含：`<Input_PubKey_A>`、`<Input_Signature_A>`。

7. OP_CHECKSIG verifies the signature (`<Input_Signature_A>`) against the public key (`<Input_PubKey_A>`). If the signature is valid, it pushes `true` onto the stack; otherwise, it pushes `false`. Assuming the signature is valid, the stack now contains: `true`. Please note that the `<Input_Signature_A>` is generated by signing the entire transaction data (include other inputs and outputs) with the private key corresponding to `<Input_PubKey_A>`.
   OP_CHECKSIG 验证签名（`<Input_Signature_A>`）与公钥（`<Input_PubKey_A>`）。如果签名有效，它将 `true` 压入栈；否则，它将 `false` 压入栈。假设签名有效，栈现在包含：`true`。请注意，`<Input_Signature_A>` 是通过使用与 `<Input_PubKey_A>` 对应的私钥对整个交易数据（包括其他输入和输出）进行签名生成的。

> [!IMPORTANT]
> The last step is the most critical one, it ensures the intergrity and authenticity of the transaction. If the signature verification fails, it means that the transaction has been tampered with or that the spender does not possess the private key corresponding to the public key, and thus the UTXO cannot be spent. The miner can also not modify the transaction data (e.g., change the output value) without invalidating the signature.

> [!IMPORTANT] 重要
> 最后一步是最关键的一步，它确保了交易的完整性和真实性。如果签名验证失败，这意味着交易已被篡改，或者花费者不拥有与公钥对应的私钥，因此 UTXO 无法被花费。矿工也不能在不使签名失效的情况下修改交易数据（例如，更改输出值）。

> [!NOTE]
> This a very interesting design, Bitcoin do not store some meta data to indicate who own how much BTC, instead, it use script system to define the ownership. This make Bitcoin very flexible, for example, we can create multi-signature wallet by using different ScriptPubKey. You can also create time-lock transaction by using OP_CHECKLOCKTIMEVERIFY opcode. I will discuss it later.

> [!NOTE] 注意
> 这是一个非常有趣的设计，比特币不存储一些元数据来指示谁拥有多少 BTC，而是使用脚本系统来定义所有权。这使得比特币非常灵活，例如，我们可以通过使用不同的 ScriptPubKey 创建多签名钱包。你还可以使用 OP_CHECKLOCKTIMEVERIFY 操作码创建时间锁定交易。我稍后会讨论它。

> [!WARNING]
> Another interesting points is `Input_Signature_A` is generated by signing the entire transaction data (include other inputs and outputs) with the private key corresponding to `Input_PubKey_A`, but the signature itself is also a part of the transaction data. To solve this circular dependency, breifly, when signing the transaction, the ScriptSig fields of all inputs are set to empty (or a placeholder), then the transaction is serialized and signed. However, there are some implementation details and optimizations involved, which cause the SegWit upgrade. I will discuss it later.

> [!WARNING] 警告
> 另一个有趣的点是 `Input_Signature_A` 是通过使用与 `Input_PubKey_A` 对应的私钥对整个交易数据（包括其他输入和输出）进行签名生成的，但签名本身也是交易数据的一部分。为了解决这种循环依赖，简而言之，在签名交易时，所有输入的 ScriptSig 字段被设置为空（或占位符），然后交易被序列化和签名。然而，涉及一些实现细节和优化，这导致了 SegWit 升级。我稍后会讨论它。

---

The outputs of the transaction will create two new UTXOs, one for user B with value 0.3 BTC, and another for user A with value 0.7 BTC (the change). Since the ownership of the UTXOs is defined by ScriptPubKey, the outputs should also manufacture the ScriptPubKey accordingly.

交易的输出将创建两个新的 UTXOs，一个给用户 B，价值 0.3 BTC，另一个给用户 A，价值 0.7 BTC（找零）。由于 UTXOs 的所有权由 ScriptPubKey 定义，输出也应相应地制造 ScriptPubKey。

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

在这个例子中，我们不讨论多个输入和多个输出，但概念是相似的。输入的总价值必须等于或大于输出的总价值，如果更大，差额被视为交易费用，将由矿工收取（矿工如何收取交易费用的方式也很有趣，我稍后会讨论）。发送者需要为每个输入提供解锁脚本（ScriptSig）以证明他们有权花费 UTXOs。矿工将通过为每个输入执行连接的 ScriptSig 和 ScriptPubKey 来验证交易。如果所有输入都有效，则交易被认为是有效的。

## Where is the Account?
## 账户在哪里？

You many notice that in the above example, there is no concept of account or balance. This is because Bitcoin uses UTXO model instead of account-based model. The UTXO is like a locked check, you can only spend it if you have the right to unlock it. Imagine you want to create an new "account", you just do everything offline: generate a new private key, derive the public key, then hash the public key to get the PubKeyHash. The PubKeyHash is like your "acount number", but because the account balance is zero, so the blockchain do not need to store anything for you. When someone want to send you some BTC, they will create a transaction with an output that has a ScriptPubKey containing your PubKeyHash.

你可能注意到在上面的例子中，没有账户或余额的概念。这是因为比特币使用 UTXO 模型而不是基于账户的模型。UTXO 就像一张锁定的支票，只有你有权解锁它时才能花费它。想象你想创建一个新的"账户"，你只需离线完成所有操作：生成一个新的私钥，派生公钥，然后对公钥进行哈希以获得 PubKeyHash。PubKeyHash 就像你的"账号"，但因为账户余额为零，所以区块链不需要为你存储任何东西。当有人想给你发送一些 BTC 时，他们将创建一个交易，其输出具有包含你的 PubKeyHash 的 ScriptPubKey。

## How Transactions are Added to the Blockchain?
## 交易如何被添加到区块链？

We just discussed how transactions work in principle, but how these transactions are added to the blockchain? This is where miners come in. Each miner is a node in the Bitcoin network, it maintains a mempool of unconfirmed transactions.

我们刚刚讨论了交易在原理上是如何工作的，但这些交易是如何被添加到区块链的呢？这就是矿工的作用。每个矿工都是比特币网络中的一个节点，它维护一个未确认交易的内存池。

If you want to send some BTC to someone, you need to create a transaction and broadcast it to the network. The transaction will be propagated to all nodes and be added to their mempool.

如果你想给某人发送一些 BTC，你需要创建一个交易并将其广播到网络。交易将被传播到所有节点并添加到它们的内存池中。

Miners will select transactions from their mempool by **using their own strategy** (usually based on transaction fees). Each block can have multiple transactions, but the total size of the block must not exceed 4 MB (since SegWit upgrade). A block contains the following fields:

矿工将通过**使用他们自己的策略**（通常基于交易费用）从他们的内存池中选择交易。每个区块可以有多个交易，但区块的总大小不得超过 4 MB（自 SegWit 升级以来）。一个区块包含以下字段：

- **Block Header**: contains metadata about the block, includes:
  **区块头**：包含关于区块的元数据，包括：

  - **Version**: 4 bits, indicates the version of the block.
    **版本**：4 位，表示区块的版本。

  - **Previous Block Hash**: 32 bytes, the hash of the previous block in the blockchain, that is why it is called blockchain.
    **前一个区块哈希**：32 字节，区块链中前一个区块的哈希，这就是为什么它被称为区块链。

  - **Merkle Root**: 32 bytes, the root hash of the Merkle tree of all transactions included in the block.
    **Merkle 根**：32 字节，区块中包含的所有交易的 Merkle 树的根哈希。

  - **Timestamp**: 4 bytes, the time when the block was created.
    **时间戳**：4 字节，区块创建的时间。

  - **Difficulty Target**: 4 bytes, the target threshold for the block hash.
    **难度目标**：4 字节，区块哈希的目标阈值。

  - **Nonce**: 4 bytes, a counter used for the proof-of-work algorithm.
    **随机数（Nonce）**：4 字节，用于工作量证明算法的计数器。

- **Block Body**: contains a list of transactions included in the block.
  **区块体**：包含区块中包含的交易列表。

  - **Transaction Count**: a variable-length integer indicating the number of transactions in the block.
    **交易数量**：一个可变长度整数，表示区块中的交易数量。

  - **Transactions**: a list of transactions included in the block.
    **交易**：区块中包含的交易列表。

    - **Coinbase Transaction**: a special transaction that rewards the miner for creating the block.
      **Coinbase 交易**：一个特殊的交易，奖励矿工创建区块。

    - **Regular Transactions**: transactions selected from the mempool.
      **常规交易**：从内存池中选择的交易。

- **SegWit Data** (if applicable): contains witness data for SegWit transactions.
  **SegWit 数据**（如果适用）：包含 SegWit 交易的见证数据。

> [!NOTE]
> SegWit (Segregated Witness) is an upgrade to the Bitcoin protocol that separates the witness data (signatures) from the transaction data. It is also a very interesting concept, because it is hard to upgrade a running blockchain system in institution level. I will discuss it later.

> [!NOTE] 注意
> SegWit（隔离见证）是对比特币协议的升级，它将见证数据（签名）与交易数据分离。这也是一个非常有趣的概念，因为在机构层面升级正在运行的区块链系统是很困难的。我稍后会讨论它。

When a miner want to create a new block, it will first select transactions from its mempool, then construct the block body. Next, it will create the block header, create the Merkle tree from the transactions to get the Merkle root, set the previous block hash to the hash of the latest block in the blockchain, set the timestamp to the current time, set the difficulty target based on the network difficulty, and start the proof-of-work process.

当矿工想要创建一个新区块时，它将首先从其内存池中选择交易，然后构建区块体。接下来，它将创建区块头，从交易创建 Merkle 树以获得 Merkle 根，将前一个区块哈希设置为区块链中最新区块的哈希，将时间戳设置为当前时间，根据网络难度设置难度目标，并开始工作量证明过程。

### What is Merkle Tree ?
### 什么是 Merkle 树？

The merkle tree is a binary tree where each leaf node is the hash of a transaction, and each non-leaf node is the hash of the concatenation of its two child nodes. The Merkle root is the topmost node of the tree, it provides a compact representation of all transactions in the block and allows for efficient verification of transaction inclusion. For example, if we have four transactions: Tx1, Tx2, Tx3, and Tx4, the Merkle tree would be constructed as follows:

Merkle 树是一个二叉树，其中每个叶节点是一个交易的哈希，每个非叶节点是其两个子节点连接的哈希。Merkle 根是树的最顶层节点，它提供了区块中所有交易的紧凑表示，并允许高效验证交易包含。例如，如果我们有四个交易：Tx1、Tx2、Tx3 和 Tx4，Merkle 树将按如下方式构建：

```
        Merkle Root
        /          \
   Hash12        Hash34
   /    \        /     \
Hash1  Hash2  Hash3   Hash4
```

If we add two more transactions in the new block: Tx5 and Tx6, the new Merkle tree would look like this:

如果我们在新区块中添加两个交易：Tx5 和 Tx6，新的 Merkle 树将如下所示：

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

如你所见，旧的 Merkle 根仍然是新 Merkle 树的一部分，这意味着前一个区块中的所有交易仍然包含在新区块中。Merkle 树的结构允许高效验证交易包含，因为只需要检查少量哈希即可验证交易是否包含在区块中。

### What is Proof-of-Work?
### 什么是工作量证明？

The proof-of-work process involves finding a nonce such that the hash of the block header is less than the difficulty target. The formula is:

工作量证明过程涉及找到一个随机数，使得区块头的哈希小于难度目标。公式是：

$$
\text{Sha256}(\text{Sha256}(\text{BlockHeader})) < \text{DifficultyTarget}
$$

The miner will increment the nonce and recalculate the hash until it finds a valid nonce. Once a valid nonce is found, the miner will broadcast the new block to the network. Other nodes will verify the block by checking the proof-of-work, validating all transactions in the block, and ensuring that the block follows the consensus rules. If the block is valid, it will be added to the blockchain, and the miner will receive the block reward (newly minted Bitcoin) and transaction fees from all transactions included in the block.

矿工将递增随机数并重新计算哈希，直到找到有效的随机数。一旦找到有效的随机数，矿工将向网络广播新区块。其他节点将通过检查工作量证明、验证区块中的所有交易并确保区块遵循共识规则来验证区块。如果区块有效，它将被添加到区块链中，矿工将收到区块奖励（新铸造的比特币）和区块中包含的所有交易的交易费用。

### What is the structure of Coinbase Transaction?
### Coinbase 交易的结构是什么？

Coinbase transaction is a special type of transaction that is created by miners to claim the block reward and transaction fees for mining a new block. It is the first transaction in a block and has no inputs. It does not have UTXO inputs, or we can assume that its input are all rest of the transactions in the block. The structure of a coinbase transaction includes:

Coinbase 交易是一种特殊类型的交易，由矿工创建以索取挖掘新区块的区块奖励和交易费用。它是区块中的第一笔交易，没有输入。它没有 UTXO 输入，或者我们可以假设它的输入是区块中所有其余的交易。Coinbase 交易的结构包括：

- **Inputs**: contains a single input with a special script called the coinbase script.
  **输入**：包含一个带有称为 coinbase 脚本的特殊脚本的单个输入。

- **Outputs**: contains one or more outputs that specify the amount of Bitcoin being rewarded to the miner and any transaction fees collected from other transactions in the block.
  **输出**：包含一个或多个输出，指定奖励给矿工的比特币数量以及从区块中其他交易收取的任何交易费用。

The reward amount have two parts:

奖励金额有两部分：

1. **Block Reward**: this is the newly minted Bitcoin that is created with each block. The block reward started at 50 BTC in 2009 and halves approximately every four years (210,000 blocks). As of 2024, the block reward is 6.25 BTC, and it will halve to 3.125 BTC in 2024.
   **区块奖励**：这是随每个区块创建的新铸造的比特币。区块奖励在 2009 年从 50 BTC 开始，大约每四年（210,000 个区块）减半一次。截至 2024 年，区块奖励为 6.25 BTC，并将在 2024 年减半至 3.125 BTC。

2. **Transaction Fees**: this is the total amount of transaction fees collected from all transactions included in the block. Each transaction can include a fee that is paid to the miner who includes it in the block.
   **交易费用**：这是从区块中包含的所有交易收取的交易费用总额。每笔交易都可以包含一个费用，支付给将其包含在区块中的矿工。

As you can see, the transaction fee is defined by the sender of the transaction, and miners have the incentive to include transactions with higher fees in their blocks to maximize their rewards.

如你所见，交易费用由交易的发送者定义，矿工有动力在他们的区块中包含费用较高的交易以最大化他们的奖励。

## Rethinking Point 1
## 反思点 1

At that point, I already know many basic concepts of Bitcoin, I also leave some contents for later discussion, like SegWit upgrade, how scripts can be used to create multi-signature wallets and time-lock transactions, etc. But before moving on, I want to rethink some questions to ensure I really understand these concepts.

到这一点，我已经知道了比特币的许多基本概念，我也留下了一些内容以供稍后讨论，如 SegWit 升级、如何使用脚本创建多签名钱包和时间锁定交易等。但在继续之前，我想重新思考一些问题以确保我真正理解这些概念。

#### Q1: If Miner decides which transactions to include in the block, it is possible every miner have different mempool, and thus create different blocks? How the network reach consensus in this case?

#### Q1：如果矿工决定在区块中包含哪些交易，那么每个矿工可能有不同的内存池，因此创建不同的区块？在这种情况下网络如何达成共识？

> A: Yes, it is possible that different miners have different mempools and thus create different blocks. However, the Bitcoin network uses a consensus mechanism called Nakamoto Consensus to ensure that all nodes agree on the state of the blockchain. When a miner creates a new block, it broadcasts the block to the network. Other nodes will verify the block and add it to their local copy of the blockchain if it is valid. If two miners create different blocks at the same time (a fork), nodes will temporarily have different versions of the blockchain. However, as more blocks are added to the chain, one branch will become longer than the other, and nodes will switch to the longest valid chain. This process ensures that all nodes eventually agree on a single version of the blockchain.

> A：是的，不同的矿工可能有不同的内存池，因此创建不同的区块。然而，比特币网络使用一种称为中本聪共识（Nakamoto Consensus）的共识机制来确保所有节点就区块链的状态达成一致。当矿工创建一个新区块时，它将区块广播到网络。其他节点将验证区块，如果有效，则将其添加到其本地区块链副本中。如果两个矿工同时创建不同的区块（分叉），节点将暂时具有不同版本的区块链。然而，随着更多的区块被添加到链中，一个分支将变得比另一个分支更长，节点将切换到最长的有效链。这个过程确保所有节点最终就区块链的单一版本达成一致。

> On the other hand, find the valid nonce is a hard problem, every ten minutes on average only one miner can find the valid nonce, this make the forking event very rare. Hence, the network can almost always reach consensus. The answer can also used to exlpain how to prevent the evil miner to create invalid blocks, because the evil miner need to redo the proof-of-work for the invalid block, which is computationally expensive.

> 另一方面，找到有效的随机数是一个困难的问题，平均每十分钟只有一个矿工可以找到有效的随机数，这使得分叉事件非常罕见。因此，网络几乎总是可以达成共识。这个答案也可以用来解释如何防止恶意矿工创建无效区块，因为恶意矿工需要为无效区块重新进行工作量证明，这在计算上是昂贵的。

#### Q2: What if over 50% of the mining power is controlled by evil miners? Can they create invalid blocks and double spend?

#### Q2：如果超过 50% 的挖矿算力被恶意矿工控制怎么办？他们能创建无效区块并双重支付吗？

> A: If over 50% of the mining power is controlled by evil miners, they can potentially create invalid blocks and double spend. This is known as a 51% attack. In such an attack, the evil miners can create a longer chain of blocks that includes their double-spent transactions. However, it may also make the price of Bitcoin drop significantly, which is not in the interest of the evil miners themselves.

> A：如果超过 50% 的挖矿算力被恶意矿工控制，他们可能会创建无效区块并双重支付。这被称为 51% 攻击。在这样的攻击中，恶意矿工可以创建一个包含他们双重支付交易的更长的区块链。然而，这也可能使比特币的价格大幅下跌，这不符合恶意矿工自己的利益。

> These attacker owns a large portion of the mining power, they also have a significant investment in the Bitcoin network. If they attack the network and cause the price of Bitcoin to drop, they may suffer significant financial losses. Therefore, while a 51% attack is theoretically possible, it is not necessarily in the best interest of the attackers to carry it out.

> 这些攻击者拥有大部分挖矿算力，他们也在比特币网络中有大量投资。如果他们攻击网络并导致比特币价格下跌，他们可能会遭受重大财务损失。因此，虽然 51% 攻击在理论上是可能的，但进行攻击不一定符合攻击者的最佳利益。

#### Q3: If we create a isolated Bitcoin network, will it cause there are two different Bitcoin networks? How does it effect the price of Bitcoin?

#### Q3：如果我们创建一个隔离的比特币网络，会导致有两个不同的比特币网络吗？这如何影响比特币的价格？

> A: Yes, if we create an isolated Bitcoin network that is not connected to the main Bitcoin network, it will result in two separate Bitcoin networks. It is actually happened before, for example, Bitcoin Cash and Bitcoin SV are two separate networks that were created as a result of hard forks from the main Bitcoin network. Every user own 1 BTC in the main network will also own 1 BCH or 1 BSV in the new networks.

> A：是的，如果我们创建一个不与主比特币网络连接的隔离比特币网络，将导致两个独立的比特币网络。这实际上以前发生过，例如，比特币现金（Bitcoin Cash）和比特币 SV（Bitcoin SV）是作为主比特币网络硬分叉的结果创建的两个独立网络。在主网络中拥有 1 BTC 的每个用户也将在新网络中拥有 1 BCH 或 1 BSV。

> ##### 1. Two Ways to Create a Network
> ##### 1. 创建网络的两种方式

> * **Scenario A: The "Clone" (Independent Network)**
> If you take the Bitcoin source code and start a brand-new chain from scratch (a new "Genesis Block"), you have created a new cryptocurrency (like Litecoin).
> * **Effect:** It has **zero effect** on the original Bitcoin. It's like printing your own "Monopoly" money; it doesn't make the US Dollar any less valuable.

> * **场景 A："克隆"（独立网络）**
> 如果你使用比特币源代码并从头开始一个全新的链（一个新的"创世区块"），你就创建了一个新的加密货币（如莱特币）。
> * **效果：**它对原始比特币**没有任何影响**。这就像印刷你自己的"大富翁"钱；它不会使美元变得不那么有价值。

> * **Scenario B: The "Hard Fork" (Shared History)**
> This happens when you take the existing Bitcoin ledger but change the rules moving forward. This is what happened with **Bitcoin Cash (BCH)** and **Bitcoin SV (BSV)**.
> * **The "Free Money" Effect:** Because the history is shared, anyone who held **1 BTC** on the original chain at the moment of the split suddenly finds they also own **1 BCH** on the new chain.

> * **场景 B："硬分叉"（共享历史）**
> 这发生在你采用现有的比特币分类账但向前改变规则时。这就是**比特币现金（BCH）**和**比特币 SV（BSV）**发生的情况。
> * **"免费金钱"效应：**因为历史是共享的，任何在分裂时刻在原始链上持有 **1 BTC** 的人突然发现他们在新链上也拥有 **1 BCH**。

> ##### 2. The Impact on Price: "Code is Cheap, Consensus is Expensive"
> ##### 2. 对价格的影响："代码便宜，共识昂贵"

> While you can easily copy the **code**, you cannot easily copy the **Social Consensus**. This is why the price of the original Bitcoin usually remains dominant:

> 虽然你可以轻松复制**代码**，但你不能轻松复制**社会共识**。这就是为什么原始比特币的价格通常保持主导地位：

> * **Network Effects:** The value of Bitcoin comes from the millions of users, merchants, and developers using it. A new, isolated network starts with zero users, making its tokens worth very little.
> * **Security (Hash Power):** Miners follow the profit. Since the original Bitcoin has the highest price, it attracts the most computing power, making it the most secure. An isolated network with low hash power is vulnerable to **51% attacks**.
> * **Market Dilution:** In 2017, many feared that forks would dilute the 21-million-cap. However, the market quickly realized that "Bitcoin" is a brand tied to the most secure chain. The price of forks usually trends downward relative to BTC over time.

> * **网络效应：**比特币的价值来自使用它的数百万用户、商家和开发者。一个新的、孤立的网络从零用户开始，使其代币价值很小。
> * **安全性（哈希算力）：**矿工追随利润。由于原始比特币的价格最高，它吸引了最多的计算能力，使其最安全。一个哈希算力低的孤立网络容易受到 **51% 攻击**。
> * **市场稀释：**在 2017 年，许多人担心分叉会稀释 2100 万的上限。然而，市场很快意识到"比特币"是一个与最安全链绑定的品牌。随着时间的推移，分叉的价格通常相对于 BTC 呈下降趋势。

#### Q4. The creator of a transaction need to indicate the input UTXOs, but how they provide the information of UTXOs to the miner? Do they need provide the ID of UTXOs? If so, how the miner can find the UTXOs from the ID?

#### Q4. 交易的创建者需要指示输入 UTXOs，但他们如何向矿工提供 UTXOs 的信息？他们需要提供 UTXOs 的 ID 吗？如果是，矿工如何从 ID 中找到 UTXOs？

> A: Yes, the creator of a transaction needs to specify the input UTXOs by providing the transaction ID (TxID) and the output index of each UTXO being spent. The TxID is a unique identifier for each transaction, which is calculated by hashing the serialized transaction data. The output index indicates which output of the transaction is being spent (since a transaction can have multiple outputs).

> A：是的，交易的创建者需要通过提供交易 ID（TxID）和每个被花费的 UTXO 的输出索引来指定输入 UTXOs。TxID 是每个交易的唯一标识符，通过对序列化的交易数据进行哈希计算得出。输出索引表示正在花费交易的哪个输出（因为一个交易可以有多个输出）。

> When a miner receives a transaction, it can look up the UTXOs in its local copy of the blockchain. Each node maintains a database of all UTXOs, which is updated whenever a new block is added to the blockchain. The miner can use the TxID and output index provided in the transaction to find the corresponding UTXO in its database. If the UTXO exists and is unspent, the miner can then verify the transaction by executing the unlocking script (ScriptSig) against the locking script (ScriptPubKey) of the UTXO.

> 当矿工收到一个交易时，它可以在其本地区块链副本中查找 UTXOs。每个节点维护所有 UTXOs 的数据库，每当将新区块添加到区块链时都会更新该数据库。矿工可以使用交易中提供的 TxID 和输出索引在其数据库中找到相应的 UTXO。如果 UTXO 存在且未花费，矿工可以通过针对 UTXO 的锁定脚本（ScriptPubKey）执行解锁脚本（ScriptSig）来验证交易。

#### Q5. How TxID stored in the Blockchain?

#### Q5. TxID 如何存储在区块链中？

> The TxID is not explicitly stored in the blockchain; instead, it is derived from the transaction data itself. When a transaction is created, it is serialized into a byte format, and then a double SHA-256 hash of this serialized data is computed to produce the TxID. This means that the TxID is a unique fingerprint of the transaction.

> TxID 没有明确存储在区块链中；相反，它是从交易数据本身派生的。当创建交易时，它被序列化为字节格式，然后计算此序列化数据的双 SHA-256 哈希以生成 TxID。这意味着 TxID 是交易的唯一指纹。

#### Q6. What will happen if two different transactions have the same TxID?

#### Q6. 如果两个不同的交易具有相同的 TxID 会发生什么？

> In 2012, two coinbase transactions were found to have the same TxID due to a bug in the Bitcoin software. One miner receive same reward to same address twice. This event is known as a [BIP-34](https://github.com/bitcoin/bips/blob/master/bip-0034.mediawiki). The Bitcoin network fix it by requiring that the block height be included in the coinbase transaction, which ensures that each coinbase transaction has a unique TxID.

> 在 2012 年，由于比特币软件中的一个错误，发现两个 coinbase 交易具有相同的 TxID。一个矿工两次收到相同地址的相同奖励。这个事件被称为 [BIP-34](https://github.com/bitcoin/bips/blob/master/bip-0034.mediawiki)。比特币网络通过要求在 coinbase 交易中包含区块高度来修复它，这确保每个 coinbase 交易都有唯一的 TxID。

## Who decides the difficulty target?
## 谁决定难度目标？

The difficulty target is adjusted every 2016 blocks (approximately every two weeks) to ensure that blocks are mined at an average rate of one block every 10 minutes. The adjustment is based on the time it took to mine the previous 2016 blocks. If the blocks were mined faster than the target time, the difficulty will increase; if they were mined slower, the difficulty will decrease. This mechanism ensures that the Bitcoin network maintains a consistent block time despite changes in the total mining power of the network.

难度目标每 2016 个区块（大约每两周）调整一次，以确保区块以平均每 10 分钟一个区块的速度被挖掘。调整基于挖掘前 2016 个区块所花费的时间。如果区块的挖掘速度快于目标时间，难度将增加；如果挖掘速度较慢，难度将降低。这种机制确保比特币网络保持一致的区块时间，尽管网络的总挖矿算力发生变化。

But who controls it in a decentralized network? The answer is that it is controlled by the consensus rules of the Bitcoin protocol. All nodes in the network follow the same rules for adjusting the difficulty target, and miners must adhere to these rules when creating new blocks. If a miner attempts to create a block with an invalid easier or harder difficulty target, other nodes will reject the block. This ensures that the difficulty target is consistently applied across the entire network.

但在去中心化网络中谁控制它？答案是它由比特币协议的共识规则控制。网络中的所有节点都遵循相同的规则来调整难度目标，矿工在创建新区块时必须遵守这些规则。如果矿工试图创建一个具有无效的更容易或更难的难度目标的区块，其他节点将拒绝该区块。这确保难度目标在整个网络中一致应用。

## How to write the custom locking script?
## 如何编写自定义锁定脚本？

Although the script itself allow very flexible logic, in practice, most transactions use a few standard script templates for security and compatibility reasons. The non-standard scripts may not be relayed or mined by all nodes, which can lead to transaction delays or failures. The most common standard script types are:

尽管脚本本身允许非常灵活的逻辑，但在实践中，出于安全和兼容性原因，大多数交易使用几个标准脚本模板。非标准脚本可能不会被所有节点中继或挖掘，这可能导致交易延迟或失败。最常见的标准脚本类型是：

- **Pay-to-PubKey-Hash (P2PKH)**: the most common type, which we discussed earlier.
  **Pay-to-PubKey-Hash (P2PKH)**：最常见的类型，我们之前讨论过。

- **Pay-to-Script-Hash (P2SH)**: allows for more complex scripts by hashing the script and using the hash in the ScriptPubKey.
  **Pay-to-Script-Hash (P2SH)**：通过对脚本进行哈希并在 ScriptPubKey 中使用哈希来允许更复杂的脚本。

- **Multi-Signature Scripts**: require multiple signatures to spend the UTXO, often used in P2SH or P2WSH.
  **多签名脚本**：需要多个签名才能花费 UTXO，通常用于 P2SH 或 P2WSH。

- **Null Data (OP_RETURN)**: allows for storing arbitrary data in the blockchain, often used for non-financial purposes.
  **空数据（OP_RETURN）**：允许在区块链中存储任意数据，通常用于非金融目的。

- **Witness （SegWit） Scripts**: used in SegWit transactions to separate witness data from transaction data.
  **见证（SegWit）脚本**：用于 SegWit 交易以将见证数据与交易数据分离。

  - **Pay-to-Witness-PubKey-Hash (P2WPKH)**: used in SegWit transactions to separate witness data from transaction data.
    **Pay-to-Witness-PubKey-Hash (P2WPKH)**：用于 SegWit 交易以将见证数据与交易数据分离。

  - **Pay-to-Witness-Script-Hash (P2WSH)**: similar to P2SH but used in SegWit transactions.
    **Pay-to-Witness-Script-Hash (P2WSH)**：类似于 P2SH，但用于 SegWit 交易。

- **Pay-to-Taproot (P2TR)**: used in Taproot transactions, which is an upgrade that enhances privacy and flexibility.
  **Pay-to-Taproot (P2TR)**：用于 Taproot 交易，这是增强隐私和灵活性的升级。

If you want to create a custom locking script, you can use P2SH to bypass, let me use a example to illustrate how it works.

如果你想创建自定义锁定脚本，你可以使用 P2SH 来绕过，让我用一个例子来说明它是如何工作的。

1. First, you need to write your custom script, for example, a multi-signature script that requires two out of three signatures to spend the UTXO.
   首先，你需要编写你的自定义脚本，例如，一个需要三个签名中的两个才能花费 UTXO 的多签名脚本。

```
OP_2
<PubKey1>
<PubKey2>
<PubKey3>
OP_3
OP_CHECKMULTISIG
```

2. Next, you need to hash the script using SHA-256 followed by RIPEMD-160 to get the script hash.
   接下来，你需要使用 SHA-256 然后 RIPEMD-160 对脚本进行哈希以获得脚本哈希。

3. Then, you create a P2SH ScriptPubKey using the script hash.
   然后，你使用脚本哈希创建一个 P2SH ScriptPubKey。

```
OP_HASH160
<ScriptHash>
OP_EQUAL
```

4. When you want to spend the UTXO, you need to provide the original script and the required signatures in the ScriptSig.
   当你想花费 UTXO 时，你需要在 ScriptSig 中提供原始脚本和所需的签名。

```
<Empty>  # Due to a bug in OP_CHECKMULTISIG, an extra item is needed
         # 由于 OP_CHECKMULTISIG 中的一个错误，需要一个额外的项
<Signature1>
<Signature2>
<OriginalScript>
```

5. The miner will concatenate the ScriptSig and ScriptPubKey, then execute the script to verify the transaction.
   矿工将连接 ScriptSig 和 ScriptPubKey，然后执行脚本以验证交易。

## Bitcoin Upgrades
## 比特币升级

Currently, Bitcoin still have many shortcomings, the most notable one is scalability. The original design of Bitcoin can only handle about 7 transactions per second, which is far below the requirements of a global payment system. To address this issue, several upgrades have been proposed and implemented over the years, including:

目前，比特币仍有许多缺点，最显著的是可扩展性。比特币的原始设计每秒只能处理大约 7 笔交易，这远低于全球支付系统的要求。为了解决这个问题，多年来提出并实施了几项升级，包括：

- **Segregated Witness (SegWit)**: implemented in 2017, SegWit separates the witness data (signatures) from the transaction data, allowing for more transactions to fit in a block. It also fixes the transaction malleability issue, which is important for second-layer solutions like the Lightning Network.
  **隔离见证（SegWit）**：2017 年实施，SegWit 将见证数据（签名）与交易数据分离，允许在一个区块中容纳更多交易。它还修复了交易可塑性问题，这对于闪电网络等第二层解决方案很重要。

- **Taproot**: implemented in 2021, Taproot enhances privacy and flexibility by allowing complex scripts to appear as simple transactions on the blockchain. It also improves the efficiency of multi-signature transactions.
  **Taproot**：2021 年实施，Taproot 通过允许复杂脚本在区块链上显示为简单交易来增强隐私和灵活性。它还提高了多签名交易的效率。

- **Lightning Network**: a second-layer (L2) solution that enables fast and low-cost transactions by creating off-chain payment channels between users. It leverages the security of the Bitcoin blockchain while allowing for instant transactions.
  **闪电网络**：一种第二层（L2）解决方案，通过在用户之间创建链外支付通道来实现快速和低成本的交易。它利用比特币区块链的安全性，同时允许即时交易。

Before moving on, I want to discuss why upgrade is possible in a decentralized network? Because it seems we need majority of the nodes to agree on the upgrade, otherwise, it may cause a hard fork.

在继续之前，我想讨论为什么在去中心化网络中可能进行升级？因为似乎我们需要大多数节点同意升级，否则可能会导致硬分叉。

Briefly, the upgraude happens through social and technical consensus, which meams everyone believe the upgrade is beneficial to the network. The upgrade process usually involves several steps:

简而言之，升级通过社会和技术共识进行，这意味着每个人都相信升级对网络有益。升级过程通常涉及几个步骤：

1. **Proposal**: a Bitcoin Improvement Proposal (BIP) is created to outline the details of the upgrade.
   **提案**：创建比特币改进提案（BIP）以概述升级的细节。

2. **Discussion**: the proposal is discussed within the Bitcoin community, including developers, miners, and users.
   **讨论**：在比特币社区内讨论该提案，包括开发者、矿工和用户。

3. **Implementation**: the upgrade is implemented in the Bitcoin software.
   **实施**：在比特币软件中实施升级。

4. **Activation**: the upgrade is activated through a signaling mechanism, where miners signal their support for the upgrade by including a specific bit in the block header. Once a certain threshold of blocks signal support, the upgrade is activated.
   **激活**：通过信号机制激活升级，矿工通过在区块头中包含特定位来表示他们对升级的支持。一旦一定数量的区块表示支持，升级就会被激活。

To better understand the consensus mechanism, we can revise a famous battle which is "Block Size War". In 2017, there was a debate within the Bitcoin community about whether to increase the block size limit to improve scalability. Some members of the community believed that increasing the block size would allow for more transactions to be processed per block, while others argued that it would lead to centralization and security risks. To resolve this debate, a proposal called Segregated Witness (SegWit) was introduced, which not only increased the effective block size but also addressed transaction malleability issues.

为了更好地理解共识机制，我们可以回顾一场著名的战斗，即"区块大小之战"。2017 年，比特币社区内就是否增加区块大小限制以提高可扩展性展开了辩论。社区的一些成员认为增加区块大小将允许每个区块处理更多交易，而其他人则认为这将导致中心化和安全风险。为了解决这场辩论，引入了一个名为隔离见证（SegWit）的提案，它不仅增加了有效的区块大小，还解决了交易可塑性问题。

But big blockers were not satisfied with SegWit alone, they wanted a direct increase in the block size limit. This led to the creation of Bitcoin Cash (BCH) in August 2017, which implemented a larger block size limit of 8 MB. The split resulted in two separate cryptocurrencies: Bitcoin (BTC) and Bitcoin Cash (BCH). Some miners are also do not want to accept SegWit upgrade, then the User-Activated Soft Fork (UASF) mechanism was proposed, which allowed users to signal their support for the upgrade by running software that enforced the new rules. This put pressure on miners to adopt the upgrade, as they risked losing support from users if they did not comply. Eventually, the majority of miners adopted SegWit, and it was activated on the Bitcoin network in August 2017. This event proofs that

但大区块支持者对单独的 SegWit 不满意，他们想要直接增加区块大小限制。这导致了 2017 年 8 月比特币现金（BCH）的创建，它实施了 8 MB 的更大区块大小限制。分裂导致了两个独立的加密货币：比特币（BTC）和比特币现金（BCH）。一些矿工也不想接受 SegWit 升级，然后提出了用户激活软分叉（UASF）机制，该机制允许用户通过运行强制执行新规则的软件来表示他们对升级的支持。这给矿工施加了压力以采用升级，因为如果他们不遵守，他们可能会失去用户的支持。最终，大多数矿工采用了 SegWit，它于 2017 年 8 月在比特币网络上激活。这个事件证明了：

> Users, not miners, ultimately control the Bitcoin network.

> 用户，而不是矿工，最终控制比特币网络。

## SegWit Upgrade
## SegWit 升级

The SegWit upgrade is a significant improvement to the Bitcoin protocol. First, it resolves a critical vulnerability known as Quadratic Sighash Problem. Recall the Locking Script and Unlocking Script we discussed earlier, the last step is to verify the signature by using `OP_CHECKSIG` opcode. If we check the algiorithm of signature verification or generation, we will find its complexity is $O(n^2)$, where is the number of inputs. If an attacker create a transaction with many inputs, it will cause the signature verification to take a long time, which can be exploited to launch a denial-of-service (DoS) attack on the network.

SegWit 升级是对比特币协议的重大改进。首先，它解决了一个被称为二次签名哈希问题（Quadratic Sighash Problem）的关键漏洞。回想我们之前讨论的锁定脚本和解锁脚本，最后一步是使用 `OP_CHECKSIG` 操作码验证签名。如果我们检查签名验证或生成的算法，我们会发现它的复杂度是 $O(n^2)$，其中 n 是输入的数量。如果攻击者创建一个有许多输入的交易，它将导致签名验证花费很长时间，这可以被利用来对网络发起拒绝服务（DoS）攻击。

The original algorithm of signature generation and verification is as follows: A transaction have $n$ inputs, each input contains a ScriptSig and a reference to a UTXO, which means we need to geneate $n$ signatures for each input, each signature generation process be like:

签名生成和验证的原始算法如下：一个交易有 $n$ 个输入，每个输入包含一个 ScriptSig 和对 UTXO 的引用，这意味着我们需要为每个输入生成 $n$ 个签名，每个签名生成过程如下：

1. Create a copy of the transaction.
   创建交易的副本。

2. For each input in the transaction copy, set the ScriptSig to an empty script (or a placeholder), except for the input being signed, which retains its original ScriptSig.
   对于交易副本中的每个输入，将 ScriptSig 设置为空脚本（或占位符），除了正在签名的输入，它保留其原始 ScriptSig。

3. Serialize the modified transaction copy.
   序列化修改后的交易副本。

4. Hash the serialized transaction using SHA-256 twice to produce a message digest.
   使用 SHA-256 两次对序列化的交易进行哈希以生成消息摘要。

5. Use the private key corresponding to the public key in the ScriptSig to sign the message digest, producing the signature.
   使用 ScriptSig 中公钥对应的私钥对消息摘要进行签名，生成签名。

6. Insert the generated signature into the ScriptSig of the input being signed.
   将生成的签名插入正在签名的输入的 ScriptSig 中。

The pseudocode for the above algorithm is as follows:

上述算法的伪代码如下：

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

如我们所见，对于每个输入，我们需要序列化和哈希整个交易，每个输入的交易格式都不同，这意味着总复杂度是 $O(n^2)$。为了解决这个问题，SegWit 引入了一种新的方法来计算签名哈希（sighash），它将见证数据（签名）与交易数据分离。新算法如下：

1. Create a copy of the transaction.
   创建交易的副本。

2. For each input in the transaction copy, set the ScriptSig to an empty script (or a placeholder). (**different from the original algorithm**)
   对于交易副本中的每个输入，将 ScriptSig 设置为空脚本（或占位符）。（**与原始算法不同**）

3. Serialize the modified transaction copy without the witness data.
   序列化修改后的交易副本，不包括见证数据。

4. Hash the serialized transaction using SHA-256 twice to produce a message digest.
   使用 SHA-256 两次对序列化的交易进行哈希以生成消息摘要。

5. Use the private key corresponding to the public key in the ScriptSig to sign the message digest, producing the signature.
   使用 ScriptSig 中公钥对应的私钥对消息摘要进行签名，生成签名。

6. Insert the generated signature into the witness data of the input being signed. (**different from the original algorithm**)
   将生成的签名插入正在签名的输入的见证数据中。（**与原始算法不同**）

The pseudocode for the new algorithm is as follows:

新算法的伪代码如下：

```cpp
Transaction txCopy = transaction;
for (auto& in : txCopy.inputs) {
    in.scriptSig = EmptyScript; // Set all ScriptSigs to empty
                                 // 将所有 ScriptSigs 设置为空
}
uint8_t[] serializedTx = SerializeWithoutWitness(txCopy);
uint8_t[] messageDigest = SHA256(SHA256(serializedTx));
for (auto &input : transaction.inputs) {
    uint8_t[] signature = Sign(messageDigest, input.privateKey);
    transaction.witnessData.insert(signature);
}
```

By separating the witness data from the transaction data, SegWit allows for more efficient signature generation and verification, reducing the complexity to $O(n)$.

通过将见证数据与交易数据分离，SegWit 允许更有效的签名生成和验证，将复杂度降低到 $O(n)$。

**You may want to ask why we need to separate the witness data from the transaction data but not insert them into placeholder in ScriptSig?** The answer is because of *Transaction Malleability Attack* and *lightning network* (L2 solutions).

**你可能想问为什么我们需要将见证数据与交易数据分离，而不是将它们插入 ScriptSig 中的占位符？**答案是因为*交易可塑性攻击*和*闪电网络*（L2 解决方案）。

The speed of transaction of bitcoin is very slow because we generate a new block every 10 minutes, to improve the speed, someone propose the concept of L2 solutions, which means we can create a second layer on top of the Bitcoin blockchain to handle transactions off-chain, while still leveraging the security of the underlying blockchain. The most notable L2 solution is the Lightning Network.

比特币的交易速度非常慢，因为我们每 10 分钟生成一个新区块，为了提高速度，有人提出了 L2 解决方案的概念，这意味着我们可以在比特币区块链之上创建第二层来处理链外交易，同时仍然利用底层区块链的安全性。最著名的 L2 解决方案是闪电网络。

However, *Transaction Malleability Attack* is a critical issue that needs to be addressed before implementing L2 solutions. Transaction malleability refers to the ability to modify a transaction's ID (TxID) without changing its content. This can cause problems for L2 solutions, for example, considering following scenario of Exchange like Binance:

然而，*交易可塑性攻击*是在实施 L2 解决方案之前需要解决的关键问题。交易可塑性是指在不改变其内容的情况下修改交易 ID（TxID）的能力。这可能会给 L2 解决方案带来问题，例如，考虑以下类似币安的交易所的场景：

1. User A wants to deposit 1 BTC to Binance.
   用户 A 想要向币安存入 1 BTC。

2. Binance provides User A with a deposit address and waits for the transaction to be confirmed on the Bitcoin blockchain.
   币安为用户 A 提供存款地址，并等待交易在比特币区块链上确认。

3. User A creates a transaction to send 1 BTC to the deposit address.
   用户 A 创建一个交易以向存款地址发送 1 BTC。

4. An attacker intercepts the transaction and modifies it in a way that changes its TxID.
   攻击者拦截交易并以改变其 TxID 的方式修改它。

5. The modified transaction is confirmed on the Bitcoin blockchain, but Binance is still waiting for the original transaction with the original TxID.
   修改后的交易在比特币区块链上确认，但币安仍在等待具有原始 TxID 的原始交易。

6. User A's deposit is not recognized by Binance, leading to confusion and potential loss of funds.
   用户 A 的存款未被币安识别，导致混乱和潜在的资金损失。

You may want to ask why Binance do not ask the user to provide the confirmed transaction details? The answer is Binance can do it but it means the user need to wait much longer time which will cause the meaning of using L2 solution is lost. The another question is how the attacker can modify the transaction id without changing its content? I will discuss it in another article because most of them content is related to the cryptographic algorithm.

你可能想问为什么币安不要求用户提供确认的交易详细信息？答案是币安可以这样做，但这意味着用户需要等待更长的时间，这将导致使用 L2 解决方案的意义丧失。另一个问题是攻击者如何在不改变其内容的情况下修改交易 ID？我将在另一篇文章中讨论它，因为大部分内容与加密算法有关。

After fixing the two issues, blockchain can support L2 solutions like Lightning Network in principle. I will discuss its principle later.

在修复这两个问题后，区块链原则上可以支持闪电网络等 L2 解决方案。我稍后会讨论它的原理。

## Taproot Upgrade
## Taproot 升级

The main purpose of Taproot upgrade is to enhance privacy and flexibility of Bitcoin transactions. Originally, complex transactions, such as multi-signature transactions or those with time-lock conditions, were easily identifiable on the blockchain. For example, a multi-signature transaction would reveal the public keys involved and the number of required signatures. This transparency could potentially expose user behavior and transaction patterns.

Taproot 升级的主要目的是增强比特币交易的隐私和灵活性。最初，复杂交易，如多签名交易或具有时间锁定条件的交易，在区块链上很容易识别。例如，多签名交易会揭示涉及的公钥和所需签名的数量。这种透明度可能会暴露用户行为和交易模式。

To resolve this multi-signature transaction privacy issue, Taproot introduces Schnorr signatures ([BIP 340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki)), which allow multiple signatures to be aggregated into a single signature. This means that a multi-signature transaction can appear identical to a standard single-signature transaction on the blockchain, enhancing privacy.

为了解决这个多签名交易隐私问题，Taproot 引入了 Schnorr 签名（[BIP 340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki)），它允许将多个签名聚合成一个签名。这意味着多签名交易可以在区块链上显示为与标准单签名交易相同，从而增强隐私。

> [!NOTE]
> Of course, the signature algorithm is determined by the ScriptPubKey, so we need to create a new ScriptPubKey to support Schnorr signatures. The new ScriptPubKey is called Pay-to-Taproot (P2TR), which uses a new opcode `OP_CHECKSIGADD` ([BIP 342](https://github.com/bitcoin/bips/blob/master/bip-0342.mediawiki)) to verify Schnorr signatures.
>
> I have another question when I leaned the Schnorr signature, which is why the privacy is so important? The answer is because Bitcoin is pseudonymous, meaning that while transactions are public, the identities of the users behind those transactions are not directly linked to their Bitcoin addresses. However, with enough analysis, it is possible to link addresses to real-world identities, especially when users reuse addresses or interact with centralized services like exchanges. Enhancing privacy helps protect users from such analysis and potential targeting.

> [!NOTE] 注意
> 当然，签名算法由 ScriptPubKey 确定，所以我们需要创建一个新的 ScriptPubKey 来支持 Schnorr 签名。新的 ScriptPubKey 称为 Pay-to-Taproot（P2TR），它使用一个新的操作码 `OP_CHECKSIGADD`（[BIP 342](https://github.com/bitcoin/bips/blob/master/bip-0342.mediawiki)）来验证 Schnorr 签名。
>
> 当我学习 Schnorr 签名时，我有另一个问题，那就是为什么隐私如此重要？答案是因为比特币是假名的，这意味着虽然交易是公开的，但这些交易背后的用户身份并不直接链接到他们的比特币地址。然而，通过足够的分析，可以将地址链接到现实世界的身份，特别是当用户重复使用地址或与中心化服务（如交易所）交互时。增强隐私有助于保护用户免受此类分析和潜在针对。

The another feature of Taproot is to allow complex scripts to be hidden unless they are needed. For example, if a UTXO can be spent by any one of conditions is met, these cnditions may be:

Taproot 的另一个特性是允许隐藏复杂脚本，除非需要它们。例如，如果 UTXO 可以在满足任何一个条件时被花费，这些条件可能是：

- A single signature from Alice.
  Alice 的单个签名。

- If Alice is unavailable for a certain period, then two signatures from Bob and Charlie.
  如果 Alice 在一定时间内不可用，则来自 Bob 和 Charlie 的两个签名。

- If the transaction is not spent within a certain time frame, then a signature from Dave.
  如果交易在一定时间内未花费，则来自 Dave 的签名。

Please note that all these conditions are represented as scripts, if we have 5 scripts, we can combine them into a Merkle tree, the Merkle tree can be represented as follows in any forms, here are some examples:

请注意，所有这些条件都表示为脚本，如果我们有 5 个脚本，我们可以将它们组合成一个 Merkle 树，Merkle 树可以以任何形式表示如下，这里有一些例子：

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

然后我们需要展示如果有人想使用条件 S3 来花费 UTXO 会发生什么。UTXO 只会存储一个：

$$
P_{\text{tweaked}}=P_{\text{internal}}+H(P_{internal||Root})G
$$

it is a formula related to eclipse curve, to avoid to understand too many cryptographic concepts, we can care about how to use it. First, the UTXO only store `P_tweaked`, which is exactly same as a normal UTXO storing a public key. If some one want to spend the UTXO, there are two ways to do it.

这是一个与椭圆曲线相关的公式，为了避免理解太多的加密概念，我们可以关心如何使用它。首先，UTXO 只存储 `P_tweaked`，这与普通 UTXO 存储公钥完全相同。如果有人想花费 UTXO，有两种方法可以做到。

#### Key Path Spending
#### 密钥路径花费

Provide a signature of the transaction using the private key corresponding to `P_tweaked`. The signature may be a Schnorr signature of mutiple parties if `P_tweaked` is derived from multiple public keys.

使用与 `P_tweaked` 对应的私钥提供交易的签名。如果 `P_tweaked` 是从多个公钥派生的，则签名可能是多方的 Schnorr 签名。

> [!NOTE]
> You may confuse why the path even need to exist, our original plan is to use the UTXO when one of the scripts is satisfied, but now we can use the public key to spend it directly? It looks like we construct a backdoor to bypass all scripts. The answer is also privacy, such design we can make the UTXO exactly same as normal before we use it in Script Path Spending (will discuss later). However, if we hope to ban the Key Path Spending, we can provide a `P_internal` that no one know the corresponding private key, then the only way to spend the UTXO is through Script Path Spending.

> [!NOTE] 注意
> 你可能会困惑为什么这条路径甚至需要存在，我们的原始计划是在满足其中一个脚本时使用 UTXO，但现在我们可以直接使用公钥花费它？看起来我们构建了一个后门来绕过所有脚本。答案也是隐私，这样的设计我们可以在脚本路径花费中使用它之前使 UTXO 与正常的完全相同（稍后会讨论）。然而，如果我们希望禁止密钥路径花费，我们可以提供一个没有人知道相应私钥的 `P_internal`，那么花费 UTXO 的唯一方法是通过脚本路径花费。

#### Script Path Spending
#### 脚本路径花费

Provide:

提供：

- $P_{\text{internal}}$
- The Merkle proof from the root to the script S3, which will be like follows if we use the first Merkle tree structure above:
  从根到脚本 S3 的 Merkle 证明，如果我们使用上面的第一个 Merkle 树结构，它将如下所示：

```
        Root
        /  \
   Hash12  Hash345
            /   \
        S3    Hash45
```

As you can say, we only provide a subset of the Merkle tree, so that others even can not know the number of scripts in the Merkle tree. They can only infer that there are at least three scripts.

如你所说，我们只提供 Merkle 树的一个子集，因此其他人甚至不知道 Merkle 树中脚本的数量。他们只能推断至少有三个脚本。

> [!NOTE]
> In practice, we can organize the tree in Huffman coding way to minimize the size of Merkle proof. For example, if S3 is used more frequently than S4 and S5, we can make S3 closer to the root.

> [!NOTE] 注意
> 在实践中，我们可以以霍夫曼编码的方式组织树，以最小化 Merkle 证明的大小。例如，如果 S3 比 S4 和 S5 使用得更频繁，我们可以使 S3 更接近根。

Now the miner need to verify the spending request, it will first compute:

现在矿工需要验证花费请求，它将首先计算：

1. Compute $P_{\text{tweaked}}$ using the provided $P_{\text{internal}}$ and the Merkle root.
   使用提供的 $P_{\text{internal}}$ 和 Merkle 根计算 $P_{\text{tweaked}}$。

2. Verify the signature using $P_{\text{tweaked}}$.
   使用 $P_{\text{tweaked}}$ 验证签名。

3. Verify the provided script S3 by executing it with the transaction data.
   通过使用交易数据执行提供的脚本 S3 来验证它。

4. Verify the Merkle proof to ensure that S3 is indeed part of the Merkle tree represented by the root.
   验证 Merkle 证明以确保 S3 确实是由根表示的 Merkle 树的一部分。

## Rethinking Point 2
## 反思点 2

#### Q: In the Script Path Spending of Taproot, we may find we can remove the $P_{\text{internal}}$ and only keep the Merkle root in the UTXO, but why the design still keep $P_{\text{internal}}$?

#### Q: 在 Taproot 的脚本路径花费中，我们可能会发现我们可以删除 $P_{\text{internal}}$ 并在 UTXO 中只保留 Merkle 根，但为什么设计仍然保留 $P_{\text{internal}}$？

> A: The reason to keep $P_{\text{internal}}$ is to allow for Key Path Spending, which provides an additional way to spend the UTXO. By including $P_{\text{internal}}$, the UTXO can be spent directly using a signature corresponding to $P_{\text{tweaked}}$, without needing to reveal any scripts or Merkle proofs. This enhances privacy, as the UTXO can appear identical to a standard single-signature transaction on the blockchain.

> A：保留 $P_{\text{internal}}$ 的原因是允许密钥路径花费，这提供了一种花费 UTXO 的额外方式。通过包含 $P_{\text{internal}}$，UTXO 可以直接使用与 $P_{\text{tweaked}}$ 对应的签名来花费，而无需揭示任何脚本或 Merkle 证明。这增强了隐私，因为 UTXO 可以在区块链上显示为与标准单签名交易相同。

> To be honest, I am not very understand this part. I believe the main reason is I do not fully understand why such kind of privacy is important. I will try to learn more about it later. But it definitely make the design more elegant because it is compatible with the original UTXO design.

> 老实说，我不太理解这部分。我相信主要原因是我不完全理解为什么这种隐私如此重要。我稍后会尝试更多地了解它。但它确实使设计更加优雅，因为它与原始 UTXO 设计兼容。

## Summary
## 总结

In this article, I do not discuss the detail of:

在本文中，我没有讨论以下细节：

- Proof of why concensus can be reached in a decentralized network, I tend to understand them through intuitive way.
  为什么在去中心化网络中可以达成共识的证明，我倾向于通过直观的方式理解它们。

- Details of Cryptographic algorithms, like ECDSA and Schnorr signature. Actually, I think most cryptographic algorithms follows the same "API" of RSA design, I do not need consider too much about the implementation of API. The API can have mutiply backends, but we also need to notice the difference of security level of different algorithms.
  加密算法的细节，如 ECDSA 和 Schnorr 签名。实际上，我认为大多数加密算法遵循 RSA 设计的相同"API"，我不需要太多考虑 API 的实现。API 可以有多个后端，但我们还需要注意不同算法的安全级别的差异。

- Details of L2 solutions, like Lightning Network. I think it is better to discuss them when we use Ethereum, because Ethereum have more flexible smart contract design.
  L2 解决方案的细节，如闪电网络。我认为当我们使用以太坊时讨论它们更好，因为以太坊有更灵活的智能合约设计。
