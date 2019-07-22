#!/usr/bin/env python3
# Copyright (c) 2015-2019 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""
Test SIGHASH_NOINPUT soft-fork enabled floating Update transaction can be replaced by Update transactions with increasing nSequence values.
"""
import copy
from decimal import Decimal
import struct
import time

from test_framework.authproxy import JSONRPCException
from test_framework.blocktools import (
    add_witness_commitment,
    create_block,
    create_coinbase,
    create_tx_with_script,
    get_legacy_sigopcount_block,
)
from test_framework.key import ECKey
from test_framework.messages import (
    CBlock,
    COIN,
    COutPoint,
    CScriptWitness,
    CTransaction,
    CTxIn,
    CTxInWitness,
    CTxOut,
    NODE_NETWORK,
    NODE_WITNESS,
    MAX_BLOCK_BASE_SIZE,
    ToHex,
    ser_uint256,
    ser_string,
    uint256_from_compact,
    uint256_from_str,
)
from test_framework.mininode import P2PDataStore

from test_framework.script import (
    CScript,
    CScriptOp,
    CScriptNum,
    OP_0,
    OP_1, 
    OP_2,
    OP_2DUP,
    OP_3DUP,
    OP_2DROP,
    OP_CHECKLOCKTIMEVERIFY, 
    OP_CHECKMULTISIG,
    OP_CHECKMULTISIGVERIFY,
    OP_CHECKSEQUENCEVERIFY,
    OP_CHECKSIG,
    OP_CHECKSIGVERIFY,
    OP_DUP,
    OP_EQUALVERIFY,
    OP_HASH160,
    OP_DROP,
    OP_ELSE,
    OP_ENDIF,
    OP_EQUAL,
    OP_FALSE,
    OP_HASH160,
    OP_IF,
    OP_INVALIDOPCODE,
    OP_NOTIF,
    OP_RETURN,
    OP_TRUE,
    SIGHASH_ALL,
    SIGHASH_ANYPREVOUT,
    SIGHASH_NONE,
    SIGHASH_SINGLE,
    SIGHASH_ALLINPUT,
    SIGHASH_ANYONECANPAY,
    SIGHASH_ANYPREVOUT,
    SIGHASH_NOINPUT,
    SIGHASH_ANYPREVOUTANYSCRIPT,
    SegwitVersion1SignatureHash,
    SignatureHash,
    hash160,
    hash256,
    sha256,
    uint256_from_str
)
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
    bytes_to_hex_str,
    hex_str_to_bytes,
)

from data import invalid_txs

def int_to_bytes(x) -> bytes:
    return x.to_bytes((x.bit_length() + 7) // 8, 'big')

def get_p2pkh_script(pubkey):
    """Get the script associated with a P2PKH."""
    return CScript([OP_DUP, OP_HASH160, hash160(pubkey), OP_EQUALVERIFY, OP_CHECKSIG])

def get_p2pkh_script_witness(sig, pubkey):
    script_witness = CScriptWitness()
    script_witness.stack = [sig, pubkey]
    return script_witness

def get_multisig_script(pubkey1, pubkey2):
    """Get the script associated with a P2PKH."""
    return CScript([OP_2, pubkey1, pubkey2, OP_2, OP_CHECKMULTISIG]) 

def get_multisig_script_witness(sig1, sig2, witness_program):
    script_witness = CScriptWitness()
    script_witness.stack = [b'', sig1, sig2, witness_program]
    return script_witness

# sign a P2PKH output, using the key we know about
# this signs input inIdx in tx, which is assumed to be spending output outIdx in spend_tx
def sign_tx(tx, spend_tx, key, inIdx, outIdx):
    scriptPubKey = bytearray(spend_tx.vout[outIdx].scriptPubKey)
    if (scriptPubKey[0] == OP_TRUE):  # an anyone-can-spend
        tx.vin[inIdx].scriptSig = CScript()
        return
    (sighash, err) = SignatureHash(spend_tx.vout[outIdx].scriptPubKey, tx, inIdx, SIGHASH_ALL)
    sig = key.sign_ecdsa(sighash) + bytes(bytearray([SIGHASH_ALL]))
    tx.vin[inIdx].scriptSig = CScript([sig])

class NoInputTests(BitcoinTestFramework):

    def get_eltoo_update_script(self, state):
        """Get the script associated with a P2PKH."""
        # BASE_RELATIVE_LOCKTIME = 10
        CLTV_START_TIME = 500000000

        # or(1@and(older(100),thresh(2,pk(C),pk(C))),
        # 9@and(after(1000),thresh(2,pk(C),pk(C)))),
        return CScript([
            OP_2, self.UPDATE_PUBKEY[0], self.UPDATE_PUBKEY[1], OP_2, OP_CHECKMULTISIG,
            OP_NOTIF,
            OP_2, self.SETTLE_PUBKEY[0][state], self.SETTLE_PUBKEY[1][state], OP_2, OP_CHECKMULTISIGVERIFY,
            CScriptNum(self.csv_delay), OP_CHECKSEQUENCEVERIFY,
            OP_ELSE,
            CScriptNum(CLTV_START_TIME+state), OP_CHECKLOCKTIMEVERIFY,
            OP_ENDIF
        ])

    def get_eltoo_update_script_witness(self, state, is_update, sig1, sig2):
        witness_program = self.get_eltoo_update_script(state)
        script_witness = CScriptWitness()
        if (is_update):
            script_witness.stack = [b'', sig1, sig2, witness_program]
        else:
            script_witness.stack = [b'', sig1, sig2, b'', b'', b'', witness_program]
        return script_witness

    def add_eltoo_input(self, state, spend_state, is_update):
        #   disable sequence locks for update transactions
        if is_update is True:
            csv_timelock = 0xfffffffe
        else:
            csv_timelock = self.csv_delay

        #   add channel input
        self.ELTOO_TX[state].vin = [ CTxIn(outpoint = COutPoint(self.ELTOO_TX[spend_state].sha256, 0), scriptSig = b"", nSequence=csv_timelock) ]

    def add_eltoo_output(self, state):
        #   build witness program
        witness_program = self.get_eltoo_update_script(state)
        witness_hash = sha256(witness_program)
        script_wsh = CScript([OP_0, witness_hash])

        self.log.debug("ADD_ELTOO_OUTPUT: state=%s, channel_amount=%s, witness_hash=%s\n",
            state, self.CHANNEL_AMOUNT, bytes_to_hex_str(witness_hash))

        #   set tx version 2 for BIP-68 outputs with relative timelocks
        self.ELTOO_TX[state].nVersion = 2

        #   add channel output
        self.ELTOO_TX[state].vout = [ CTxOut(self.CHANNEL_AMOUNT, script_wsh) ] # channel balance

        #   initialize channel state
        CLTV_START_TIME = 500000000
        self.ELTOO_TX[state].nLockTime = CLTV_START_TIME + state

    def sign_update_tx(self, is_update, signerIdx, state, spend_state):
        if (is_update):
            privkey = self.UPDATE_PRIVKEY[signerIdx]
        else:
            privkey = self.SETTLE_PRIVKEY[signerIdx][spend_state]

        witness_program = CScript() # self.get_eltoo_update_script(spend_state), ignored because of NOINPUT
        channel_amount = self.CHANNEL_AMOUNT
        tx_hash = SegwitVersion1SignatureHash(witness_program, self.ELTOO_TX[state], 0, SIGHASH_ANYPREVOUT | SIGHASH_SINGLE, channel_amount)
        signature = privkey.sign_ecdsa(tx_hash) + chr(SIGHASH_ANYPREVOUT | SIGHASH_SINGLE).encode('latin-1')

        self.log.debug("SIGN_UPDATE_TX: state=%d, signerIdx=%d, tx_hash=%s\n", state, signerIdx, bytes_to_hex_str(tx_hash))

        return signature

    def add_eltoo_witness(self, state, spend_state, is_update):
        #   generate signatures for current state 
        sig1 = self.sign_update_tx(is_update, 0, state, spend_state)
        sig2 = self.sign_update_tx(is_update, 1, state, spend_state)

        #   add the p2wsh witness script to spend from a previous eltoo state
        self.ELTOO_TX[state].wit.vtxinwit = [ CTxInWitness() ]
        self.ELTOO_TX[state].wit.vtxinwit[0].scriptWitness = self.get_eltoo_update_script_witness(spend_state, is_update, sig1, sig2)

        #   confirm it in the mempool
        tx_hex = bytes_to_hex_str(self.ELTOO_TX[state].serialize_with_witness())
        spend_tx_hex = bytes_to_hex_str(self.ELTOO_TX[state].serialize_with_witness())

    def initialize_eltoo(self):
        # create public/private keys for nodes 2 nodes/signers
        self.UPDATE_PRIVKEY = []
        self.UPDATE_PUBKEY = []
        self.SETTLE_PRIVKEY = []
        self.SETTLE_PUBKEY = []
        for signer in range (self.num_signers):
            self.UPDATE_PRIVKEY.append(ECKey())
            self.UPDATE_PRIVKEY[signer].generate()
            self.UPDATE_PUBKEY.append(self.UPDATE_PRIVKEY[signer].get_pubkey().get_bytes())
            self.log.debug("\nUPDATE_PUBKEY[signer=%s]=%s\n",signer, bytes_to_hex_str(self.UPDATE_PUBKEY[signer]))

            # create unique key pairs for each settlement state
            self.SETTLE_PRIVKEY.append([])
            self.SETTLE_PUBKEY.append([])

            for state in range (self.num_states) :
                self.SETTLE_PRIVKEY[signer].append(ECKey())
                self.SETTLE_PRIVKEY[signer][state].generate()
                self.SETTLE_PUBKEY[signer].append(self.SETTLE_PRIVKEY[signer][state].get_pubkey().get_bytes())
                self.log.debug("\nSETTLE_PUBKEY[signer=%s][state=%s]=%s\n",signer, state, bytes_to_hex_str(self.SETTLE_PUBKEY[signer][state]))

        # create some transactions with an eltoo output, one per state of the channel
        self.ELTOO_TX = []
        for state in range(self.num_states):
            self.ELTOO_TX.append(CTransaction())

    def add_funding_tx(self, state, spend_tx, spend_key, change_amount):

        #   pay change to new p2pkh output, TODO: should use p2wpkh
        change_key = ECKey()
        change_key.generate()
        change_pubkey = change_key.get_pubkey().get_bytes()
        change_script_pkh = CScript([OP_0, hash160(change_pubkey)])

        #   add new funding input and change output
        self.ELTOO_TX[state].vin.append(CTxIn(COutPoint(spend_tx.sha256, 0), b""))
        self.ELTOO_TX[state].vout.append(CTxOut(change_amount, change_script_pkh))

        #   pay fee from spend_tx w/change output (assumed to be last txin)
        inIdx = len(self.ELTOO_TX[state].vin)-1
        
        #   sign the tx fee input w/change output
        sign_tx(self.ELTOO_TX[state], spend_tx, spend_key, inIdx, 0)

        self.ELTOO_TX[state].rehash()

        return change_key

    def commit_state(self, state, error_code=None, error_message=None):
        #   confirm it in the mempool
        self.ELTOO_TX[state].rehash()

        #   confirm it in the mempool
        tx_hex = bytes_to_hex_str(self.ELTOO_TX[state].serialize_with_witness())
        if error_code is None or error_message is None:
            txid = self.nodes[0].sendrawtransaction(tx_hex, True)
        else:
            assert_raises_rpc_error(error_code, error_message, self.nodes[0].sendrawtransaction, tx_hex)

    def set_test_params(self):
        self.num_nodes = 1
        self.setup_clean_chain = True
        self.extra_args = [[]]

    def run_test(self):
        node = self.nodes[0]  # convenience reference to the node

        self.bootstrap_p2p()  # Add one p2p connection to the node

        self.block_heights = {}
        self.coinbase_key = ECKey()
        self.coinbase_key.generate()
        self.coinbase_pubkey = self.coinbase_key.get_pubkey().get_bytes()
        self.tip = None
        self.blocks = {}
        self.genesis_hash = int(self.nodes[0].getbestblockhash(), 16)
        self.block_heights[self.genesis_hash] = 0
        self.spendable_outputs = []
        self.csv_delay = 20
        self.num_states = 10
        self.num_signers = 2

        # compute min relay fee for 1000 byte transaction
        self.FEE_AMOUNT = int(node.getnetworkinfo()['relayfee']*COIN)
        self.CHANNEL_AMOUNT = 1000000

        # Construct a bunch of sPKs that send coins back to the host wallet
        self.log.info("Constructing addresses for returning coins")
        host_spks = []
        host_pubkeys = []
        for i in range(2):
            addr = self.nodes[0].getnewaddress(address_type="legacy")
            info = self.nodes[0].getaddressinfo(addr)
            spk = hex_str_to_bytes(info['scriptPubKey'])
            host_spks.append(spk)
            host_pubkeys.append(info['pubkey'])

        blockheight = self.nodes[0].getblockheader(blockhash=self.nodes[0].getbestblockhash())['height']

        # generate mature coinbase to spend
        NUM_BUFFER_BLOCKS_TO_GENERATE = 110
        for i in range(NUM_BUFFER_BLOCKS_TO_GENERATE):
            bn = self.next_block(i)
            self.save_spendable_output()
            self.sync_blocks([bn])

        blockheight = self.nodes[0].getblockheader(blockhash=self.nodes[0].getbestblockhash())['height']

        # collect spendable outputs now to avoid cluttering the code later on
        coinbase_utxo = []
        NUM_OUTPUTS_TO_COLLECT = 33
        for i in range(NUM_OUTPUTS_TO_COLLECT):
            coinbase_utxo.append(self.get_spendable_output())

        # INITIALIZE eltoo transactions, one per state with an eltoo output
        ################
        self.initialize_eltoo()

        # SETUP:0 spend the funding transaction to a setup transaction with a P2WSH output
        ################
        self.add_eltoo_output(state=0)
        self.add_funding_tx(state=0, spend_tx=coinbase_utxo[0], spend_key=self.coinbase_key, change_amount=coinbase_utxo[0].vout[0].nValue - self.FEE_AMOUNT - self.CHANNEL_AMOUNT)
        self.commit_state(state=0)
        self.ELTOO_TX[0].rehash()

        # advance block height
        self.nodes[0].generate(25)
        blockheight = self.nodes[0].getblockheader(blockhash=self.nodes[0].getbestblockhash())['height']

        # UPDATE:1 spend the setup transaction to an update transaction with a P2WSH output
        ################
        self.add_eltoo_input(state=1, spend_state=0, is_update=False)
        self.add_eltoo_output(state=1)
        self.add_eltoo_witness(state=1, spend_state=0, is_update=False)
        self.add_funding_tx(state=1, spend_tx=coinbase_utxo[1], spend_key=self.coinbase_key, change_amount=coinbase_utxo[1].vout[0].nValue - self.FEE_AMOUNT)
        self.commit_state(state=1)

        # advance block height
        self.nodes[0].generate(2)
        blockheight = self.nodes[0].getblockheader(blockhash=self.nodes[0].getbestblockhash())['height']

        # UPDATE:2 spend the setup transaction instead of the previous update transaction with a P2WSH output
        ################
        self.add_eltoo_input(state=2, spend_state=0, is_update=True)
        self.add_eltoo_output(state=2)
        self.add_eltoo_witness(state=2, spend_state=0, is_update=True)        
        self.add_funding_tx(state=2, spend_tx=coinbase_utxo[2], spend_key=self.coinbase_key, change_amount=coinbase_utxo[2].vout[0].nValue - self.FEE_AMOUNT*9)
        self.commit_state(state=2, error_code=-25, error_message="Missing inputs")

        # UPDATE:2b spend the previous update transaction to an update transaction with a P2WSH output
        ################
        self.add_eltoo_input(state=2, spend_state=1, is_update=True)
        self.add_eltoo_output(state=2)
        self.add_eltoo_witness(state=2, spend_state=1, is_update=True)
        self.add_funding_tx(state=2, spend_tx=coinbase_utxo[2], spend_key=self.coinbase_key, change_amount=coinbase_utxo[2].vout[0].nValue - self.FEE_AMOUNT)
        self.commit_state(state=2)

        # advance block height
        self.nodes[0].generate(25)
        blockheight = self.nodes[0].getblockheader(blockhash=self.nodes[0].getbestblockhash())['height']

        # UPDATE:4 spend the state 2b transaction
        ################
        self.add_eltoo_input(state=4, spend_state=2, is_update=True)
        self.add_eltoo_output(state=4)
        self.add_eltoo_witness(state=4, spend_state=2, is_update=True)
        self.add_funding_tx(state=4, spend_tx=coinbase_utxo[4], spend_key=self.coinbase_key, change_amount=coinbase_utxo[4].vout[0].nValue - self.FEE_AMOUNT)
        self.commit_state(state=4)

        # advance block height by only 10 blocks
        self.nodes[0].generate(10)
        blockheight = self.nodes[0].getblockheader(blockhash=self.nodes[0].getbestblockhash())['height']

        # UPDATE:3 trying to spend state 4 from state 3, should raise error: 'Locktime requirement not satisfied'
        ################
        self.add_eltoo_input(state=3, spend_state=4, is_update=True)
        self.add_eltoo_output(state=3)
        self.add_eltoo_witness(state=3, spend_state=4, is_update=True)
        self.add_funding_tx(state=3, spend_tx=coinbase_utxo[3], spend_key=self.coinbase_key, change_amount=coinbase_utxo[3].vout[0].nValue - self.FEE_AMOUNT)
        self.commit_state(state=3, error_code=-26, error_message="non-mandatory-script-verify-flag")

        # UPDATE:5 spend the state 4 transaction with settle transaction too soon
        ################
        self.add_eltoo_input(state=5, spend_state=4, is_update=False)
        self.add_eltoo_output(state=5)
        self.add_eltoo_witness(state=5, spend_state=4, is_update=False)
        self.add_funding_tx(state=5, spend_tx=coinbase_utxo[5], spend_key=self.coinbase_key, change_amount=coinbase_utxo[5].vout[0].nValue - self.FEE_AMOUNT)
        self.commit_state(state=5, error_code=-26, error_message="non-BIP68-final")

        # advance block height by 10 more blocks
        self.nodes[0].generate(11)
        blockheight = self.nodes[0].getblockheader(blockhash=self.nodes[0].getbestblockhash())['height']

        # UPDATE:5b spend the state 4 transaction with settle transaction > 20 blocks
        ################
        self.add_eltoo_input(state=5, spend_state=4, is_update=False)
        self.add_eltoo_output(state=5)
        self.add_eltoo_witness(state=5, spend_state=4, is_update=False)
        self.add_funding_tx(state=5, spend_tx=coinbase_utxo[5], spend_key=self.coinbase_key, change_amount=coinbase_utxo[5].vout[0].nValue - self.FEE_AMOUNT)
        self.commit_state(state=5)

    # Helper methods
    ################

    def add_transactions_to_block(self, block, tx_list):
        [tx.rehash() for tx in tx_list]
        block.vtx.extend(tx_list)

    def test_witness_block(node, p2p, block, accepted, with_witness=True, reason=None):
        """Send a block to the node and check that it's accepted
            - Submit the block over the p2p interface
            - use the getbestblockhash rpc to check for acceptance."""
        reason = [reason] if reason else []
        with node.assert_debug_log(expected_msgs=reason):
            p2p.send_message(msg_witness_block(block) if with_witness else msg_block(block))
            p2p.sync_with_ping()
            assert_equal(node.getbestblockhash() == block.hash, accepted)

    ####################################################

    # this is a little handier to use than the version in blocktools.py
    def create_tx(self, spend_tx, n, value, script=CScript([OP_TRUE, OP_DROP] * 15 + [OP_TRUE])):
        return create_tx_with_script(spend_tx, n, amount=value, script_pub_key=script)

    def next_block(self, number, spend=None, additional_coinbase_value=0, script=CScript([OP_TRUE]), solve=True, *, version=1):
        if self.tip is None:
            base_block_hash = self.genesis_hash
            block_time = int(time.time()) + 1
        else:
            base_block_hash = self.tip.sha256
            block_time = self.tip.nTime + 1
        # First create the coinbase
        height = self.block_heights[base_block_hash] + 1
        coinbase = create_coinbase(height, self.coinbase_pubkey)
        coinbase.vout[0].nValue += additional_coinbase_value
        coinbase.rehash()
        if spend is None:
            block = create_block(base_block_hash, coinbase, block_time, version=version)
        else:
            coinbase.vout[0].nValue += spend.vout[0].nValue - 1  # all but one satoshi to fees
            coinbase.rehash()
            block = create_block(base_block_hash, coinbase, block_time, version=version)
            tx = self.create_tx(spend, 0, 1, script)  # spend 1 satoshi
            sign_tx(tx, spend)
            self.add_transactions_to_block(block, [tx])
            block.hashMerkleRoot = block.calc_merkle_root()
        if solve:
            block.solve()
        self.tip = block
        self.block_heights[block.sha256] = height
        assert number not in self.blocks
        self.blocks[number] = block
        return block

    # save the current tip so it can be spent by a later block
    def save_spendable_output(self):
        self.log.debug("saving spendable output %s" % self.tip.vtx[0])
        self.spendable_outputs.append(self.tip)

    # get an output that we previously marked as spendable
    def get_spendable_output(self):
        self.log.debug("getting spendable output %s" % self.spendable_outputs[0].vtx[0])
        return self.spendable_outputs.pop(0).vtx[0]

    # move the tip back to a previous block
    def move_tip(self, number):
        self.tip = self.blocks[number]

    # adds transactions to the block and updates state
    def update_block(self, block_number, new_transactions):
        block = self.blocks[block_number]
        self.add_transactions_to_block(block, new_transactions)
        old_sha256 = block.sha256
        block.hashMerkleRoot = block.calc_merkle_root()
        block.solve()
        # Update the internal state just like in next_block
        self.tip = block
        if block.sha256 != old_sha256:
            self.block_heights[block.sha256] = self.block_heights[old_sha256]
            del self.block_heights[old_sha256]
        self.blocks[block_number] = block
        return block

    def bootstrap_p2p(self, timeout=10):
        """Add a P2P connection to the node.

        Helper to connect and wait for version handshake."""
        self.nodes[0].add_p2p_connection(P2PDataStore())
        # We need to wait for the initial getheaders from the peer before we
        # start populating our blockstore. If we don't, then we may run ahead
        # to the next subtest before we receive the getheaders. We'd then send
        # an INV for the next block and receive two getheaders - one for the
        # IBD and one for the INV. We'd respond to both and could get
        # unexpectedly disconnected if the DoS score for that error is 50.
        self.nodes[0].p2p.wait_for_getheaders(timeout=timeout)

    def reconnect_p2p(self, timeout=60):
        """Tear down and bootstrap the P2P connection to the node.

        The node gets disconnected several times in this test. This helper
        method reconnects the p2p and restarts the network thread."""
        self.nodes[0].disconnect_p2ps()
        self.bootstrap_p2p(timeout=timeout)

    def sync_blocks(self, blocks, success=True, reject_reason=None, force_send=False, reconnect=False, timeout=60):
        """Sends blocks to test node. Syncs and verifies that tip has advanced to most recent block.

        Call with success = False if the tip shouldn't advance to the most recent block."""
        self.nodes[0].p2p.send_blocks_and_test(blocks, self.nodes[0], success=success, reject_reason=reject_reason, force_send=force_send, timeout=timeout, expect_disconnect=reconnect)

        if reconnect:
            self.reconnect_p2p(timeout=timeout)

if __name__ == '__main__':
    NoInputTests().main()