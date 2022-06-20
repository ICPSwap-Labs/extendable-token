/*
Basic single token per canister
*/

import Cycles "mo:base/ExperimentalCycles";
import HashMap "mo:base/HashMap";
import Principal "mo:base/Principal";
import Result "mo:base/Result";
import Iter "mo:base/Iter";
import Text "mo:base/Text";
import Array "mo:base/Array";
import Option "mo:base/Option";
import P "mo:base/Prelude";

//Get the path right
import AID "../motoko/util/AccountIdentifier";
import ExtCore "../motoko/ext/Core";
import ExtCommon "../motoko/ext/Common";
import ExtAllowance "../motoko/ext/Allowance";

actor class standard_token(init_name: Text, init_symbol: Text, init_decimals: Nat8, init_supply: ExtCore.Balance, init_owner: Principal) = this{
  
  // Types
  type AccountIdentifier = ExtCore.AccountIdentifier;
  type SubAccount = ExtCore.SubAccount;
  type User = ExtCore.User;
  type Balance = ExtCore.Balance;
  type TokenIdentifier = ExtCore.TokenIdentifier;
  type Extension = ExtCore.Extension;
  type CommonError = ExtCore.CommonError;
  type NotifyService = ExtCore.NotifyService;
  
  type BalanceRequest = ExtCore.BalanceRequest;
  type BalanceResponse = ExtCore.BalanceResponse;
  type TransferRequest = ExtCore.TransferRequest;
  type TransferResponse = ExtCore.TransferResponse;
  type Metadata = ExtCommon.Metadata;
  type AllowanceRequest = ExtAllowance.AllowanceRequest;
  type ApproveRequest = ExtAllowance.ApproveRequest;
  
  private let EXTENSIONS : [Extension] = ["@ext/common", "@ext/allowance",];
  
  //State work
  private stable let ownerAccount : AccountIdentifier = AID.fromPrincipal(init_owner, null);
  private stable var _balancesState : [(AccountIdentifier, Balance)] = [(AID.fromPrincipal(init_owner, null), init_supply)];
  private var _balances : HashMap.HashMap<AccountIdentifier, Balance> = HashMap.fromIter(_balancesState.vals(), 0, AID.equal, AID.hash);
  private stable var allowanceEntries : [(AccountIdentifier, [(AccountIdentifier, Nat)])] = [];
  private var allowances : HashMap.HashMap<AccountIdentifier, HashMap.HashMap<AccountIdentifier, Nat>> = HashMap.HashMap<AccountIdentifier, HashMap.HashMap<AccountIdentifier, Nat>>(1, Text.equal, Text.hash);
  private stable let METADATA : Metadata = #fungible({
    name = init_name;
    symbol = init_symbol;
    decimals = init_decimals;
    metadata = null;
  }); 
  private stable var _supply : Balance  = init_supply;
  
  //State functions
  system func preupgrade() {
    _balancesState := Iter.toArray(_balances.entries());
    var size : Nat = allowances.size();
    var temp : [var (AccountIdentifier, [(AccountIdentifier, Nat)])] = Array.init<(AccountIdentifier, [(AccountIdentifier, Nat)])>(size, (ownerAccount, []));
    size := 0;
    for ((k, v) in allowances.entries()) {
      temp[size] := (k, Iter.toArray(v.entries()));
      size += 1;
    };
  };
  system func postupgrade() {
    _balances := HashMap.fromIter<AccountIdentifier, Nat>(_balancesState.vals(), 1, Text.equal, Text.hash);
    _balancesState := [];
    for ((k, v) in allowanceEntries.vals()) {
      let allowed_temp = HashMap.fromIter<AccountIdentifier, Nat>(v.vals(), 1, Text.equal, Text.hash);
      allowances.put(k, allowed_temp);
    };
    allowanceEntries := [];
  };
  
  public shared(msg) func transfer(request: TransferRequest) : async TransferResponse {
    if (ExtCore.TokenIdentifier.isPrincipal(request.token, Principal.fromActor(this)) == false) {
			return #err(#InvalidToken(request.token));
		};
    if (ExtCore.TokenIdentifier.getIndex(request.token) != 0) {
			return #err(#InvalidToken(request.token));
		};
    let sender = ExtCore.User.toAID(request.from);
    let spender = AID.fromPrincipal(msg.caller, request.subaccount);
    let receiver = ExtCore.User.toAID(request.to);
    if (AID.equal(sender, spender) == false) {
      return #err(#Unauthorized(spender));
    };
    
    switch (_balances.get(sender)) {
      case (?sender_balance) {
        if (sender_balance >= request.amount) {
          //Remove from sender first
          var sender_balance_new : Balance = sender_balance - request.amount;
          _balances.put(sender, sender_balance_new);
          
          var provisional_amount : Balance = request.amount;
          if (request.notify) {
            switch(ExtCore.User.toPrincipal(request.to)) {
              case (?canisterId) {
                let notifier : NotifyService = actor(Principal.toText(canisterId));
                switch(await notifier.tokenTransferNotification(request.token, request.from, request.amount, request.memo)) {
                  case (?balance) {
                    provisional_amount := balance;
                  };
                  case (_) {
                    var sender_balance_new2 = switch (_balances.get(sender)) {
                      case (?sender_balance) {
                          sender_balance + request.amount;
                      };
                      case (_) {
                          request.amount;
                      };
                    };
                    _balances.put(sender, sender_balance_new2);
                    return #err(#Rejected);
                  };
                };
              };
              case (_) {
                var sender_balance_new2 = switch (_balances.get(sender)) {
                  case (?sender_balance) {
                      sender_balance + request.amount;
                  };
                  case (_) {
                      request.amount;
                  };
                };
                _balances.put(sender, sender_balance_new2);
                return #err(#CannotNotify(receiver));
              }
            };
          };
          assert(provisional_amount <= request.amount); //should never hit
          
          var receiver_balance_new = switch (_balances.get(receiver)) {
            case (?receiver_balance) {
                receiver_balance + provisional_amount;
            };
            case (_) {
                provisional_amount;
            };
          };
          _balances.put(receiver, receiver_balance_new);
          
          //Process sender refund
          if (provisional_amount < request.amount) {
            var sender_refund : Balance = request.amount - provisional_amount;
            var sender_balance_new2 = switch (_balances.get(sender)) {
              case (?sender_balance) {
                  sender_balance + sender_refund;
              };
              case (_) {
                  sender_refund;
              };
            };
            _balances.put(sender, sender_balance_new2);
          };
          
          return #ok(provisional_amount);
        } else {
          return #err(#InsufficientBalance);
        };
      };
      case (_) {
        return #err(#InsufficientBalance);
      };
    };
  };

  public shared(msg) func transferFrom(request : TransferRequest) : async TransferResponse {
    if (ExtCore.TokenIdentifier.isPrincipal(request.token, Principal.fromActor(this)) == false) {
			return #err(#InvalidToken(request.token));
		};
    if (ExtCore.TokenIdentifier.getIndex(request.token) != 0) {
			return #err(#InvalidToken(request.token));
		};
    let sender = ExtCore.User.toAID(request.from);
    let spender = AID.fromPrincipal(msg.caller, request.subaccount);
    let receiver = ExtCore.User.toAID(request.to);

    let allowed : Nat = _allowance(sender, spender);
    if (allowed < request.amount) { 
      return #err(#InsufficientAllowance); 
    };
    
    switch (_balances.get(sender)) {
      case (?sender_balance) {
        if (sender_balance >= request.amount) {
          let allowedNew : Nat = allowed - request.amount;
          if (allowedNew != 0) {
            let allowanceFrom = unwrap(allowances.get(sender));
            allowanceFrom.put(spender, allowedNew);
            allowances.put(sender, allowanceFrom);
          } else {
            if (allowed != 0) {
              let allowanceFrom = unwrap(allowances.get(sender));
              allowanceFrom.delete(spender);
              if (allowanceFrom.size() == 0) { allowances.delete(sender); }
              else { allowances.put(sender, allowanceFrom); };
            };
          };
          //Remove from sender first
          var sender_balance_new : Balance = sender_balance - request.amount;
          _balances.put(sender, sender_balance_new);
          
          var provisional_amount : Balance = request.amount;
          if (request.notify) {
            switch(ExtCore.User.toPrincipal(request.to)) {
              case (?canisterId) {
                let notifier : NotifyService = actor(Principal.toText(canisterId));
                switch(await notifier.tokenTransferNotification(request.token, request.from, request.amount, request.memo)) {
                  case (?balance) {
                    provisional_amount := balance;
                  };
                  case (_) {
                    var sender_balance_new2 = switch (_balances.get(sender)) {
                      case (?sender_balance) {
                          sender_balance + request.amount;
                      };
                      case (_) {
                          request.amount;
                      };
                    };
                    _balances.put(sender, sender_balance_new2);
                    return #err(#Rejected);
                  };
                };
              };
              case (_) {
                var sender_balance_new2 = switch (_balances.get(sender)) {
                  case (?sender_balance) {
                      sender_balance + request.amount;
                  };
                  case (_) {
                      request.amount;
                  };
                };
                _balances.put(sender, sender_balance_new2);
                return #err(#CannotNotify(receiver));
              }
            };
          };
          assert(provisional_amount <= request.amount); //should never hit
          
          var receiver_balance_new = switch (_balances.get(receiver)) {
            case (?receiver_balance) {
                receiver_balance + provisional_amount;
            };
            case (_) {
                provisional_amount;
            };
          };
          _balances.put(receiver, receiver_balance_new);
          
          //Process sender refund
          if (provisional_amount < request.amount) {
            var sender_refund : Balance = request.amount - provisional_amount;
            var sender_balance_new2 = switch (_balances.get(sender)) {
              case (?sender_balance) {
                  sender_balance + sender_refund;
              };
              case (_) {
                  sender_refund;
              };
            };
            _balances.put(sender, sender_balance_new2);
          };
          
          return #ok(provisional_amount);
        } else {
          return #err(#InsufficientBalance);
        };
      };
      case (_) {
        return #err(#InsufficientBalance);
      };
    };
  };

  public shared(msg) func approve(request: ApproveRequest) : async Result.Result<Bool, CommonError> {
    let owner : AccountIdentifier = AID.fromPrincipal(msg.caller, request.subaccount);
    let spender : AccountIdentifier = AID.fromPrincipal(request.spender, null);
    let value : Nat = request.allowance;
    if (value == 0 and Option.isSome(allowances.get(owner))) {
      let allowanceCaller = unwrap(allowances.get(owner));
      allowanceCaller.delete(spender);
      if (allowanceCaller.size() == 0) { allowances.delete(owner); }
      else { allowances.put(owner, allowanceCaller); };
    } else if (value != 0 and Option.isNull(allowances.get(owner))) {
      var temp = HashMap.HashMap<AccountIdentifier, Nat>(1, Text.equal, Text.hash);
      temp.put(spender, value);
      allowances.put(owner, temp);
    } else if (value != 0 and Option.isSome(allowances.get(owner))) {
      let allowanceCaller = unwrap(allowances.get(owner));
      allowanceCaller.put(spender, value);
      allowances.put(owner, allowanceCaller);
    };
    return #ok(true);
  };

  public query func allowance(request: AllowanceRequest) : async Result.Result<Balance, CommonError> {
    let owner : AccountIdentifier = ExtCore.User.toAID(request.owner);
    let spender : AccountIdentifier = AID.fromPrincipal(request.spender, null);
    return #ok(_allowance(owner, spender));
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

  public query func extensions() : async [Extension] {
    EXTENSIONS;
  };
  
  public query func balance(request : BalanceRequest) : async BalanceResponse {
    let aid = ExtCore.User.toAID(request.user);
    switch (_balances.get(aid)) {
      case (?balance) {
        return #ok(balance);
      };
      case (_) {
        return #ok(0);
      };
    }
  };

  public query func supply(token : TokenIdentifier) : async Result.Result<Balance, CommonError> {
    #ok(_supply);
  };
  
  public query func metadata(token : TokenIdentifier) : async Result.Result<Metadata, CommonError> {
    #ok(METADATA);
  };
  
  public query func registry() : async [(AccountIdentifier, Balance)] {
    Iter.toArray(_balances.entries());
  };
  
  //Internal cycle management - good general case
  public func acceptCycles() : async () {
    let available = Cycles.available();
    let accepted = Cycles.accept(available);
    assert (accepted == available);
  };
  public query func availableCycles() : async Nat {
    return Cycles.balance();
  };

  private func unwrap<T>(x : ?T) : T =
    switch x {
        case null { P.unreachable() };
        case (?x_) { x_ };
    };
}
