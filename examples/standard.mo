import HashMap "mo:base/HashMap";
import Principal "mo:base/Principal";
import Time "mo:base/Time";
import Iter "mo:base/Iter";
import Int "mo:base/Int";
import Array "mo:base/Array";
import Option "mo:base/Option";
import Order "mo:base/Order";
import Nat "mo:base/Nat";
import Nat64 "mo:base/Nat64";
import Int64 "mo:base/Int64";
import Result "mo:base/Result";
import Text "mo:base/Text";
import Buffer "mo:base/Buffer";
import Char "mo:base/Char";
import Blob "mo:base/Blob";
import ExperimentalCycles "mo:base/ExperimentalCycles";
import Debug "mo:base/Debug";
import Prim "mo:⛔";
import SHA256 "mo:sha256/SHA256";
import Cap "mo:cap/Cap";
import Root "mo:cap/Root";
import CapTypes "mo:cap/Types";
import PrincipalUtils "mo:ic-commons/PrincipalUtils";
import NatUtils "mo:ic-commons/NatUtils";
import TextUtils "mo:ic-commons/TextUtils";
import CollectionUtils "mo:ic-commons/CollectUtils";
import Types "../motoko/util/Types";
import AID "../motoko/util/AccountIdentifier";
import ExtCore "../motoko/ext/Core";
import ExtCommon "../motoko/ext/Common";
import ExtAllowance "../motoko/ext/Allowance";
import ExtFungible "../motoko/ext/Fungible";
import ExtFee "../motoko/ext/Fee";
import ExtTransactions "../motoko/ext/Transactions";
import ExtHolders "../motoko/ext/Holders";
import ExtLogo "../motoko/ext/Logo";

shared(msg) actor class Token(init_name: Text, init_symbol: Text, init_decimals: Nat8, init_supply: ExtCore.Balance, init_owner: Principal) = this {
    
    type NotifyService = ExtCore.NotifyService;
    type AccountIdentifier = ExtCore.AccountIdentifier;
    type SubAccount = ExtCore.SubAccount;
    type User = ExtCore.User;
    type Balance = ExtCore.Balance;
    type TokenIdentifier = ExtCore.TokenIdentifier;
    type Extension = ExtCore.Extension;
    type CommonError = ExtCore.CommonError;
    type Metadata = ExtCommon.Metadata;
    type BalanceRequest = ExtCore.BalanceRequest;
    type BalanceResponse = ExtCore.BalanceResponse;
    type TransferRequest = ExtCore.TransferRequest;
    type TransferResponse = ExtCore.TransferResponse;
    type AllowanceRequest = ExtAllowance.AllowanceRequest;
    type ApproveRequest = ExtAllowance.ApproveRequest;
    type MintRequest = ExtFungible.MintRequest;
    type Transaction = ExtTransactions.Transaction;
    type TransactionRequest = ExtTransactions.TransactionRequest;
    type TransType = ExtTransactions.TransType;
    type HoldersRequest = ExtHolders.HoldersRequest;
    type Holder = ExtHolders.Holder;


    private let EXTENSIONS : [Extension] = ["@ext/common", "@ext/allowance", "@ext/fee", "@ext/holders", "@ext/logo", "@ext/cap"];
    private let NULL_ACCOUNT : AccountIdentifier = "0000000000000000000000000000000000000000000000000000000000000000";
    
    private stable var owner : Principal = init_owner;
    private stable var ownerAccount : AccountIdentifier = PrincipalUtils.toAddress(owner); 
    private stable var decimals : Nat8 = init_decimals;
    private stable var symbol : Text = init_symbol;
    private stable var totalSupply : Balance = init_supply;
    private stable var feeToAccount : AccountIdentifier = "0000000000000000000000000000000000000000000000000000000000000001"; 
    private stable var transFee : Nat = 100000000;
    private stable var tokenLogo : Text = "";
    
    private stable var balanceEntries : [(AccountIdentifier, Nat)] = [];
    private stable var allowanceEntries : [(AccountIdentifier, [(AccountIdentifier, Nat)])] = [];
    private stable var userEntries : [(AccountIdentifier, Principal)] = [];
    private stable var index : Nat = 0;


    private var balances : HashMap.HashMap<AccountIdentifier, Nat> = HashMap.HashMap<AccountIdentifier, Nat>(1, Text.equal, Text.hash);
    private var allowances : HashMap.HashMap<AccountIdentifier, HashMap.HashMap<AccountIdentifier, Nat>> = HashMap.HashMap<AccountIdentifier, HashMap.HashMap<AccountIdentifier, Nat>>(1, Text.equal, Text.hash);
    private var users : HashMap.HashMap<AccountIdentifier, Principal> = HashMap.HashMap<AccountIdentifier, Principal>(1, Text.equal, Text.hash);

    balances.put(ownerAccount, totalSupply);
    
    private stable let METADATA : Metadata = #fungible({
        name = init_name;
        symbol = init_symbol;
        decimals = init_decimals;
        metadata = null;
        ownerAccount = ownerAccount;
    });

    private stable var rootBucketId : ?Text = null;
    private var cap: ?Cap.Cap = null;

    private func _transactionHash(_type: Text, from: Text, to: Text, value: Nat, timestamp: Int) : Text {
        let text : Text = "type=" # _type # ", from=" # from # ", to=" # to # ", value=" # Nat.toText(value) # ", timestamp=" # Int.toText(timestamp);
        var buffer : Buffer.Buffer<Nat8> = Buffer.Buffer<Nat8>(0);
        for (char in text.chars()) {
            for (n in NatUtils.nat32ToNat8Arr(Char.toNat32(char)).vals()) {
                buffer.add(n);
            };
        };
        var arr : [Nat8] = buffer.toArray();
        let digest : SHA256.Digest = SHA256.Digest();
        digest.write(arr);
        var hashBytes : [Nat8] = CollectionUtils.arrayRange(digest.sum(), 0, 32);
        
        if (hashBytes.size() < 32) {
            buffer.clear();
            for (h in hashBytes.vals()) {
                buffer.add(h);
            };
            for (i in Iter.range(hashBytes.size(), 32)) {
                buffer.add(0);
            };
            hashBytes := buffer.toArray();
        };
        return TextUtils.encode(hashBytes);
    };

    private func _chargeFee(from: AccountIdentifier, transFee: Nat) {
        if(transFee > 0) {
            _transfer(from, feeToAccount, transFee, null);
        };
    };

    private func _transfer(from: AccountIdentifier, to: AccountIdentifier, value: Nat, nonce: ?Nat) {
        let fromBalance : Nat = _balanceOf(from);
        let fromBalanceNew : Nat = fromBalance - value;
        if (fromBalanceNew != 0) { balances.put(from, fromBalanceNew); }
        else { balances.delete(from); };

        let toBalance : Nat = _balanceOf(to);
        let toBalanceNew : Nat = toBalance + value;
        if (toBalanceNew != 0) { balances.put(to, toBalanceNew); };
    };

    private func _balanceOf(who: AccountIdentifier) : Nat {
        switch (balances.get(who)) {
            case (?balance) { return balance; };
            case (_) { return 0; };
        }
    };

    private func _allowance(owner: AccountIdentifier, spender: AccountIdentifier) : Nat {
        switch(allowances.get(owner)) {
            case (?allowanceOwner) {
                switch(allowanceOwner.get(spender)) {
                    case (?allowance) { return allowance; };
                    case (_) { return 0; };
                }
            };
            case (_) { return 0; };
        }
    };
    private func _addTx(caller: Principal, _transType: TransType, _index: Nat, _from: User, _to: User, _amount: Balance, _fee: Balance, _memo: ?Blob) : async () {
        let _timestamp : Int = Time.now();
        let transType : Text = switch (_transType) {
            case (#approve) { "approve" };
            case (#transfer) { "transfer" };
            case (#mint) { "mint" };
            case (#burn) { "burn" };
        };
        let memo : [Nat8] = switch (_memo) {
            case (?m) { Blob.toArray(m); };
            case _ { [] };
        };
        let _hash : Text = _transactionHash(transType, ExtCore.User.toAID(_from), ExtCore.User.toAID(_to), _amount, _timestamp);
        let from = switch (_from) {
            case (#address address) #Text(address);
            case (#principal principal) #Text(ExtCore.User.toAID(_from));
        };
        let to = switch (_to) {
            case (#address address) #Text(address);
            case (#principal principal) #Text(ExtCore.User.toAID(_to));
        };
        ignore addRecord(
            caller, transType,
            [
                ("index", #U64(u64(_index))),
                ("from", from),
                ("to", to),
                ("amount", #Text(Nat.toText(_amount))),
                ("fee", #Text(Nat.toText(_fee))),
                ("timestamp", #I64(i64(_timestamp))),
                ("hash", #Text(_hash)),
                ("memo", #Slice(memo)),
                ("transType", #Text(transType)),
            ]
        );
    };

    private func addRecord(
        caller: Principal,
        op: Text, 
        details: [(Text, Root.DetailValue)]
        ): async () {
        let c = switch(cap) {
            case(?c) { c };
            case(_) { 
                let c = Cap.Cap(null, rootBucketId);
                switch (rootBucketId) {
                    case (?rootBucketId) {};
                    case _ {
                        try {
                            rootBucketId := await c.handshake(
                                Principal.toText(Principal.fromActor(this)),
                                2_000_000_000_000
                            );
                        } catch e {
                            //throw e;
                        };
                    };
                };
                c
            };
        };
        cap := ?c;
        let record: Root.IndefiniteEvent = {
            operation = op;
            details = details;
            caller = caller;
        };
        // don't wait for result, faster
        ignore c.insert(record);
    };

    public query func getRootBucketId() : async Text {
        switch (rootBucketId) {
            case (?rootBucketId) { rootBucketId };
            case _ { "" };
        };
    };

    public func txSize() : async Nat64 {
        switch (rootBucketId) {
            case (?rootBucketId) { 
                let rootCap : Root.Self = actor(rootBucketId): Root.Self;
                await rootCap.size()
             };
            case _ { 0 };
        };
    };

    public query func extensions() : async [Extension] {
        EXTENSIONS;
    };

    public query func metadata(): async Result.Result<Metadata, CommonError> {
        return #ok(METADATA);
    };

    public query func supply(): async Result.Result<Balance, CommonError> {
        return #ok(totalSupply);
    };

    public query func balance(request : BalanceRequest) : async BalanceResponse {
        let aid : AccountIdentifier = ExtCore.User.toAID(request.user);
        return #ok(_balanceOf(aid));
    };

    public shared(msg) func approve(request: ApproveRequest) : async Result.Result<Bool, CommonError> {
        let owner : AccountIdentifier = AID.fromPrincipal(msg.caller, request.subaccount);
        if(_balanceOf(owner) < transFee) { 
            return #err(#InsufficientBalance);
        };
        let spender : AccountIdentifier = AID.fromPrincipal(request.spender, null);
        _chargeFee(owner, transFee);
        let value : Nat = request.allowance;
        let v : Nat = value + transFee;
        if (value == 0 and Option.isSome(allowances.get(owner))) {
            let allowanceCaller = Types.unwrap(allowances.get(owner));
            allowanceCaller.delete(spender);
            if (allowanceCaller.size() == 0) { allowances.delete(owner); }
            else { allowances.put(owner, allowanceCaller); };
        } else if (value != 0 and Option.isNull(allowances.get(owner))) {
            var temp = HashMap.HashMap<AccountIdentifier, Nat>(1, Text.equal, Text.hash);
            temp.put(spender, v);
            allowances.put(owner, temp);
        } else if (value != 0 and Option.isSome(allowances.get(owner))) {
            let allowanceCaller = Types.unwrap(allowances.get(owner));
            allowanceCaller.put(spender, v);
            allowances.put(owner, allowanceCaller);
        };
        users.put(owner, msg.caller);
        index := index + 1;
        ignore _addTx(msg.caller, #approve, index - 1, #principal(msg.caller), #principal(request.spender), value, transFee, null);
        return #ok(true);
    };

    public query func allowance(request: AllowanceRequest) : async Result.Result<Balance, CommonError> {
        let owner : AccountIdentifier = ExtCore.User.toAID(request.owner);
        let spender : AccountIdentifier = AID.fromPrincipal(request.spender, null);
        return #ok(_allowance(owner, spender));
    };

    private func notify(request : TransferRequest) : async () {
        switch(ExtCore.User.toPrincipal(request.to)) {
            case (?canisterId) {
                let notifier : NotifyService = actor(Principal.toText(canisterId));
                ignore notifier.tokenTransferNotification(request.token, request.from, request.amount, request.memo);
            };
            case (_) {};
        };
    };

    public shared(msg) func transfer(request : TransferRequest): async TransferResponse {
        let from : AccountIdentifier = ExtCore.User.toAID(request.from);
        let to : AccountIdentifier = ExtCore.User.toAID(request.to);
        let caller : AccountIdentifier = AID.fromPrincipal(msg.caller, request.subaccount);
        let value : Nat = request.amount;
        if (AID.equal(from, caller) == false) {
          return #err(#Unauthorized(caller));
        };
        if (value == 0) { 
            return #err(#Rejected); 
        };
        if (_balanceOf(from) < value + transFee) { 
            return #err(#InsufficientBalance); 
        };
        _chargeFee(from, transFee);
        _transfer(from, to, value, request.nonce);
        index := index + 1;
        ignore _addTx(msg.caller, #transfer, index - 1, request.from, request.to, value, transFee, Option.make(request.memo));
        if (request.notify) {
            ignore notify(request);
        };
        return #ok(value + transFee);
    };

    public shared(msg) func transferFrom(request : TransferRequest) : async TransferResponse {
        let from : AccountIdentifier = ExtCore.User.toAID(request.from);
        let to : AccountIdentifier = ExtCore.User.toAID(request.to);
        let caller : AccountIdentifier = AID.fromPrincipal(msg.caller, request.subaccount);
        let value : Nat = request.amount;        
        if (value == 0) { 
            return #err(#Rejected); 
        };
        if (_balanceOf(from) < value + transFee) { 
            return #err(#InsufficientBalance); 
        };
        let allowed : Nat = _allowance(from, caller);
        if (allowed < value + transFee) { 
            return #err(#InsufficientAllowance); 
        };

        _chargeFee(from, transFee);
        _transfer(from, to, value, request.nonce);

        let allowedNew : Nat = allowed - value - transFee;
        if (allowedNew != 0) {
            let allowanceFrom = Types.unwrap(allowances.get(from));
            allowanceFrom.put(caller, allowedNew);
            allowances.put(from, allowanceFrom);
        } else {
            if (allowed != 0) {
                let allowanceFrom = Types.unwrap(allowances.get(from));
                allowanceFrom.delete(caller);
                if (allowanceFrom.size() == 0) { allowances.delete(from); }
                else { allowances.put(from, allowanceFrom); };
            };
        };
        index := index + 1;
        ignore _addTx(getFromUser(msg.caller, from), #transfer, index - 1, request.from, request.to, value, transFee, Option.make(request.memo));
        if (request.notify) {
            ignore notify(request);
        };
        return #ok(value + transFee);
    };

    private func getFromUser(caller : Principal, from : AccountIdentifier) : Principal {
        switch(users.get(from)) {
            case (?user) { user };
            case _ { caller };
        };
    };

    public shared(msg) func mint(request: MintRequest): async TransferResponse {
        if(msg.caller != owner) {
            return #err(#Unauthorized(AID.fromPrincipal(msg.caller, null)));
        };
        let to : AccountIdentifier = ExtCore.User.toAID(request.to);
        let value : Nat = request.amount;
        let toBalance : Nat = _balanceOf(to);
        totalSupply := totalSupply + value;
        let balance : Nat = toBalance + value;
        balances.put(to, balance);
        index += 1;
        ignore _addTx(msg.caller, #mint, index - 1, #address(NULL_ACCOUNT), request.to, value, 0, null);
        return #ok(balance);
    };

    public query func getFee() : async Result.Result<Balance, CommonError> {
        return #ok(transFee);
    };
    
    public shared(msg) func setFee(_fee: Balance): async Result.Result<Bool, CommonError> {
        if(msg.caller != owner) {
            return #err(#Unauthorized(AID.fromPrincipal(msg.caller, null)));
        };
        transFee := _fee;
        return #ok(true);
    };

    public shared(msg) func setFeeTo(user: User): async Result.Result<Bool, CommonError> {
        if(msg.caller != owner) {
            return #err(#Unauthorized(AID.fromPrincipal(msg.caller, null)));
        };
        feeToAccount := ExtCore.User.toAID(user);
        return #ok(true);
    };

    public query func logo() : async Result.Result<Text, CommonError> {
        return #ok(tokenLogo);
    };
    
    public shared(msg) func setLogo(_logo: Text): async Result.Result<Bool, CommonError> {
        if(msg.caller != owner) {
            return #err(#Unauthorized(AID.fromPrincipal(msg.caller, null)));
        };
        tokenLogo := _logo;
        return #ok(true);
    };

    private func _filter(item: Transaction, user: ?User): Bool {
        switch(user) {
            case (?u) {
                let aid = ExtCore.User.toAID(u);
                if (aid == item.from or aid == item.to) {
                    return true;
                } else {
                    return false;
                };
            };
            case null {
                return true;
            }
        };
    };

    public query func totalHolders(): async Result.Result<Nat, ExtCore.CommonError> {
        return #ok(balances.size());
    };

    public query func holders(request : HoldersRequest): async Result.Result<ExtCommon.Page<Holder>, ExtCore.CommonError>{
        var buffer : Buffer.Buffer<Holder> = Buffer.Buffer<Holder>(0);
        for ((k, v) in balances.entries()) {
            buffer.add({
                account = k;
                balance = v;
            });
        };
        var allHolders : [Holder] = Array.sort<Holder>(buffer.toArray(), func (x: Holder, y: Holder) : {#less; #equal; #greater} {
            if (y.balance < x.balance) { #less }
            else if (y.balance == x.balance) { #equal }
            else { #greater }
        });
        var i : Nat = 0;
        var _start : Nat = Option.get(request.offset, 0);
        var _limit : Nat = Option.get(request.limit, 0);
        var _end : Nat = _start + _limit;
        var holders : Buffer.Buffer<Holder> = Buffer.Buffer<Holder>(0);
        label l for (holder in allHolders.vals()) {
            if (_limit == 0 or i >= _start) {
                holders.add(holder);
            };
            i := i + 1;
            if (_limit > 0 and i >= _end) {
                break l;
            };
        };
        return #ok({
            totalElements = balances.size();
            offset = _start;
            limit = _limit;
            content = holders.toArray();
        });
    };

    public query func registry() : async [(AccountIdentifier, Balance)] {
        Iter.toArray(balances.entries());
    };

    public query func cycleBalance() : async Result.Result<Nat, CommonError> {
        return #ok(ExperimentalCycles.balance());
    };

    public shared(msg) func cycleAvailable() : async Result.Result<Nat, CommonError> {
        return #ok(ExperimentalCycles.available());
    };

    private func u64(i: Nat): Nat64 {
        if (i >= 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368) {
            return 18446744073709551615;
        };
        Nat64.fromNat(i)
    };

    private func i64(i: Int): Int64 {
        Int64.fromInt(i)
    };

    /*
    * upgrade functions
    */
    system func preupgrade() {
        balanceEntries := Iter.toArray(balances.entries());
        var size : Nat = allowances.size();
        var temp : [var (AccountIdentifier, [(AccountIdentifier, Nat)])] = Array.init<(AccountIdentifier, [(AccountIdentifier, Nat)])>(size, (ownerAccount, []));
        size := 0;
        for ((k, v) in allowances.entries()) {
            temp[size] := (k, Iter.toArray(v.entries()));
            size += 1;
        };
        allowanceEntries := Array.freeze(temp);
        userEntries := Iter.toArray(users.entries());
    };

    system func postupgrade() {
        balances := HashMap.fromIter<AccountIdentifier, Nat>(balanceEntries.vals(), 1, Text.equal, Text.hash);
        balanceEntries := [];
        for ((k, v) in allowanceEntries.vals()) {
            let allowed_temp = HashMap.fromIter<AccountIdentifier, Nat>(v.vals(), 1, Text.equal, Text.hash);
            allowances.put(k, allowed_temp);
        };
        allowanceEntries := [];
        users := HashMap.fromIter<AccountIdentifier, Principal>(userEntries.vals(), 1, Text.equal, Text.hash);
        userEntries := [];
    };
};
