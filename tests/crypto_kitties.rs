//! This module tests the library's analysis capabilities on the CryptoKitties
//! `KittyCore` contract`.
#![cfg(test)]

use storage_layout_analyzer::{
    inference::abi::AbiType,
    layout::StorageSlot,
    watchdog::LazyWatchdog,
};

mod common;

/// Tests the analyser on the bytecode of the KittyCore contract deployed
/// [here](https://etherscan.io/address/0x06012c8cf97BEaD5deAe237070F9587f8E7A266d).
#[test]
fn correctly_generates_a_layout() -> anyhow::Result<()> {
    // Create the analyzer
    let bytecode = "0x6060604052600436106102a55763ffffffff60e060020a60003504166301ffc9a781146102dd5780630519ce79146103295780630560ff441461035857806305e45546146103f157806306fdde0314610416578063095ea7b3146104295780630a0f81681461044b5780630e583df01461045e57806314001f4c1461047157806318160ddd14610490578063183a7947146104a35780631940a936146104b657806319c2f201146104cc57806321717ebf146104df57806323b872dd146104f257806324e7a38a1461051a57806327d7874c146105395780632ba73c15146105585780633d7d3f5a146105775780633f4ba83a1461059657806346116e6f146105a957806346d22c70146105bf578063481af3d3146105d85780634ad8c938146105ee5780634b85fd551461060d5780634dfff04f146106235780634e0a33791461064557806356129134146106645780635663896e146106865780635c975abb1461069c5780635fd8c710146106af5780636352211e146106c2578063680eba27146106d85780636af04a57146106eb5780636fbde40d146106fe57806370a082311461071d578063715879881461073c5780637a7d49371461075b5780638456cb591461076e5780638462151c1461078157806388c2a0bf146107f357806391876e571461080957806395d89b411461081c5780639d6fac6f1461082f578063a45f4bfc1461085e578063a9059cbb14610874578063b047fb5014610896578063b0c35c05146108a9578063bc4006f5146108bc578063c3bea9af146108cf578063d3e6f49f146108e5578063defb9584146108fb578063e17b25af1461090e578063e6cbe3511461092d578063e98b7f4d14610940578063ed60ade6146109ae578063f1ca9410146109bc578063f2b47d52146109cf578063f7d8c883146109e2575b600b5433600160a060020a03908116911614806102d05750600c5433600160a060020a039081169116145b15156102db57600080fd5b005b34156102e857600080fd5b6103157fffffffff00000000000000000000000000000000000000000000000000000000600435166109f0565b604051901515815260200160405180910390f35b341561033457600080fd5b61033c610c77565b604051600160a060020a03909116815260200160405180910390f35b341561036357600080fd5b61037a600480359060248035908101910135610c86565b60405160208082528190810183818151815260200191508051906020019080838360005b838110156103b657808201518382015260200161039e565b50505050905090810190601f1680156103e35780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34156103fc57600080fd5b610404610d63565b60405190815260200160405180910390f35b341561042157600080fd5b61037a610d69565b341561043457600080fd5b6102db600160a060020a0360043516602435610da0565b341561045657600080fd5b61033c610e2a565b341561046957600080fd5b610404610e39565b341561047c57600080fd5b6102db600160a060020a0360043516610e44565b341561049b57600080fd5b610404610ef1565b34156104ae57600080fd5b610404610efc565b34156104c157600080fd5b610315600435610f02565b34156104d757600080fd5b610404610f47565b34156104ea57600080fd5b61033c610f4e565b34156104fd57600080fd5b6102db600160a060020a0360043581169060243516604435610f5d565b341561052557600080fd5b6102db600160a060020a0360043516610fe4565b341561054457600080fd5b6102db600160a060020a0360043516611091565b341561056357600080fd5b6102db600160a060020a03600435166110e3565b341561058257600080fd5b6102db600435602435604435606435611135565b34156105a157600080fd5b6102db611214565b34156105b457600080fd5b61033c6004356112ac565b34156105ca57600080fd5b6103156004356024356112c7565b34156105e357600080fd5b61033c600435611347565b34156105f957600080fd5b6102db600435602435604435606435611362565b341561061857600080fd5b6102db600435611428565b341561062e57600080fd5b6102db600160a060020a0360043516602435611448565b341561065057600080fd5b6102db600160a060020a03600435166114a2565b341561066f57600080fd5b6102db600435600160a060020a03602435166114f4565b341561069157600080fd5b6102db600435611560565b34156106a757600080fd5b6103156115c8565b34156106ba57600080fd5b6102db6115d8565b34156106cd57600080fd5b61033c600435611649565b34156106e357600080fd5b61040461166d565b34156106f657600080fd5b61033c611673565b341561070957600080fd5b6102db600160a060020a0360043516611682565b341561072857600080fd5b610404600160a060020a036004351661172f565b341561074757600080fd5b6102db600160a060020a036004351661174a565b341561076657600080fd5b6104046117d8565b341561077957600080fd5b6102db6117de565b341561078c57600080fd5b6107a0600160a060020a036004351661186a565b60405160208082528190810183818151815260200191508051906020019060200280838360005b838110156107df5780820151838201526020016107c7565b505050509050019250505060405180910390f35b34156107fe57600080fd5b61040460043561194b565b341561081457600080fd5b6102db611c1b565b341561082757600080fd5b61037a611d0e565b341561083a57600080fd5b610845600435611d45565b60405163ffffffff909116815260200160405180910390f35b341561086957600080fd5b61033c600435611d72565b341561087f57600080fd5b6102db600160a060020a0360043516602435611d8d565b34156108a157600080fd5b61033c611e30565b34156108b457600080fd5b610404611e3f565b34156108c757600080fd5b61033c611e45565b34156108da57600080fd5b6102db600435611e54565b34156108f057600080fd5b610315600435611f47565b341561090657600080fd5b610404612010565b341561091957600080fd5b6102db600160a060020a0360043516612016565b341561093857600080fd5b61033c612053565b341561094b57600080fd5b610956600435612062565b6040519915158a5297151560208a01526040808a01979097526060890195909552608088019390935260a087019190915260c086015260e0850152610100840152610120830191909152610140909101905180910390f35b6102db6004356024356121c3565b34156109c757600080fd5b610404612316565b34156109da57600080fd5b61033c61231c565b6102db60043560243561232b565b60006040517f737570706f727473496e7465726661636528627974657334290000000000000081526019016040518091039020600160e060020a03191682600160e060020a0319161480610c6f57506040517f746f6b656e4d657461646174612875696e743235362c737472696e67290000008152601d0160405180910390206040517f746f6b656e734f664f776e657228616464726573732900000000000000000000815260160160405180910390206040517f7472616e7366657246726f6d28616464726573732c616464726573732c75696e81527f7432353629000000000000000000000000000000000000000000000000000000602082015260250160405180910390206040517f7472616e7366657228616464726573732c75696e743235362900000000000000815260190160405180910390206040517f617070726f766528616464726573732c75696e74323536290000000000000000815260180160405180910390206040517f6f776e65724f662875696e743235362900000000000000000000000000000000815260100160405180910390206040517f62616c616e63654f662861646472657373290000000000000000000000000000815260120160405180910390206040517f746f74616c537570706c792829000000000000000000000000000000000000008152600d0160405180910390206040517f73796d626f6c2829000000000000000000000000000000000000000000000000815260080160405180910390206040517f6e616d652829000000000000000000000000000000000000000000000000000081526006016040518091039020181818181818181818600160e060020a03191682600160e060020a031916145b90505b919050565b600154600160a060020a031681565b610c8e612fa0565b610c96612fb2565b600d54600090600160a060020a03161515610cb057600080fd5b600d54600160a060020a031663cb4799f2878787600060405160a0015260405160e060020a63ffffffff861602815260048101848152604060248301908152604483018490529091606401848480828437820191505094505050505060a060405180830381600087803b1515610d2557600080fd5b6102c65a03f11515610d3657600080fd5b50505060405180608001805160209091016040529092509050610d59828261251d565b9695505050505050565b60115481565b60408051908101604052600d81527f43727970746f4b69747469657300000000000000000000000000000000000000602082015281565b60025460a060020a900460ff1615610db757600080fd5b610dc13382612572565b1515610dcc57600080fd5b610dd68183612592565b7f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925338383604051600160a060020a039384168152919092166020820152604080820192909252606001905180910390a15050565b600054600160a060020a031681565b662386f26fc1000081565b6000805433600160a060020a03908116911614610e6057600080fd5b5080600160a060020a0381166376190f8f6000604051602001526040518163ffffffff1660e060020a028152600401602060405180830381600087803b1515610ea857600080fd5b6102c65a03f11515610eb957600080fd5b505050604051805190501515610ece57600080fd5b600c8054600160a060020a031916600160a060020a039290921691909117905550565b600654600019015b90565b600f5481565b6000808211610f1057600080fd5b6006805483908110610f1e57fe5b600091825260209091206002909102016001015460c060020a900463ffffffff16151592915050565b6201518081565b600c54600160a060020a031681565b60025460a060020a900460ff1615610f7457600080fd5b600160a060020a0382161515610f8957600080fd5b30600160a060020a031682600160a060020a031614151515610faa57600080fd5b610fb433826125c0565b1515610fbf57600080fd5b610fc98382612572565b1515610fd457600080fd5b610fdf8383836125e0565b505050565b6000805433600160a060020a0390811691161461100057600080fd5b5080600160a060020a0381166354c15b826000604051602001526040518163ffffffff1660e060020a028152600401602060405180830381600087803b151561104857600080fd5b6102c65a03f1151561105957600080fd5b50505060405180519050151561106e57600080fd5b60108054600160a060020a031916600160a060020a039290921691909117905550565b60005433600160a060020a039081169116146110ac57600080fd5b600160a060020a03811615156110c157600080fd5b60008054600160a060020a031916600160a060020a0392909216919091179055565b60005433600160a060020a039081169116146110fe57600080fd5b600160a060020a038116151561111357600080fd5b60028054600160a060020a031916600160a060020a0392909216919091179055565b60025460a060020a900460ff161561114c57600080fd5b6111563385612572565b151561116157600080fd5b61116a84610f02565b1561117457600080fd5b600b5461118b908590600160a060020a0316612592565b600b54600160a060020a03166327ebe40a858585853360405160e060020a63ffffffff88160281526004810195909552602485019390935260448401919091526064830152600160a060020a0316608482015260a401600060405180830381600087803b15156111fa57600080fd5b6102c65a03f1151561120b57600080fd5b50505050505050565b60005433600160a060020a0390811691161461122f57600080fd5b60025460a060020a900460ff16151561124757600080fd5b600b54600160a060020a0316151561125e57600080fd5b600c54600160a060020a0316151561127557600080fd5b601054600160a060020a0316151561128c57600080fd5b601354600160a060020a0316156112a257600080fd5b6112aa6126c8565b565b600a60205260009081526040902054600160a060020a031681565b600080808085116112d757600080fd5b600084116112e457600080fd5b60068054869081106112f257fe5b9060005260206000209060020201915060068481548110151561131157fe5b9060005260206000209060020201905061132d8286838761271b565b801561133e575061133e848661289b565b95945050505050565b600960205260009081526040902054600160a060020a031681565b60025460a060020a900460ff161561137957600080fd5b6113833385612572565b151561138e57600080fd5b61139784611f47565b15156113a257600080fd5b600c546113b9908590600160a060020a0316612592565b600c54600160a060020a03166327ebe40a858585853360405160e060020a63ffffffff88160281526004810195909552602485019390935260448401919091526064830152600160a060020a0316608482015260a401600060405180830381600087803b15156111fa57600080fd5b60025433600160a060020a0390811691161461144357600080fd5b600e55565b60025460a060020a900460ff161561145f57600080fd5b6114693382612572565b151561147457600080fd5b6000908152600a602052604090208054600160a060020a031916600160a060020a0392909216919091179055565b60005433600160a060020a039081169116146114bd57600080fd5b600160a060020a03811615156114d257600080fd5b60018054600160a060020a031916600160a060020a0392909216919091179055565b60025460009033600160a060020a0390811691161461151257600080fd5b5080600160a060020a03811615156115325750600254600160a060020a03165b601154611388901061154357600080fd5b60118054600101905561155a6000808086856128f0565b50505050565b60025433600160a060020a039081169116148061158b575060005433600160a060020a039081169116145b806115a4575060015433600160a060020a039081169116145b15156115af57600080fd5b60035463ffffffff1681106115c357600080fd5b600555565b60025460a060020a900460ff1681565b600154600090819033600160a060020a039081169116146115f857600080fd5b30600160a060020a0316319150600e54600f546001010290508082111561164557600154600160a060020a031681830380156108fc0290604051600060405180830381858888f150505050505b5050565b600081815260076020526040902054600160a060020a0316801515610c7257600080fd5b61afc881565b601354600160a060020a031681565b6000805433600160a060020a0390811691161461169e57600080fd5b5080600160a060020a0381166385b861886000604051602001526040518163ffffffff1660e060020a028152600401602060405180830381600087803b15156116e657600080fd5b6102c65a03f115156116f757600080fd5b50505060405180519050151561170c57600080fd5b600b8054600160a060020a031916600160a060020a039290921691909117905550565b600160a060020a031660009081526008602052604090205490565b60005433600160a060020a0390811691161461176557600080fd5b60025460a060020a900460ff16151561177d57600080fd5b60138054600160a060020a031916600160a060020a0383161790557f450db8da6efbe9c22f2347f7c2021231df1fc58d3ae9a2fa75d39fa44619930581604051600160a060020a03909116815260200160405180910390a150565b60055481565b60025433600160a060020a0390811691161480611809575060005433600160a060020a039081169116145b80611822575060015433600160a060020a039081169116145b151561182d57600080fd5b60025460a060020a900460ff161561184457600080fd5b6002805474ff0000000000000000000000000000000000000000191660a060020a179055565b611872612fa0565b600061187c612fa0565b600080600061188a8761172f565b94508415156118ba5760006040518059106118a25750595b90808252806020026020018201604052509550611941565b846040518059106118c85750595b908082528060200260200182016040525093506118e3610ef1565b925060009150600190505b82811161193d57600081815260076020526040902054600160a060020a0388811691161415611935578084838151811061192457fe5b602090810290910101526001909101905b6001016118ee565b8395505b5050505050919050565b600080600080600080600080600260149054906101000a900460ff1615151561197357600080fd5b600680548a90811061198157fe5b60009182526020909120600290910201600181015490975067ffffffffffffffff1615156119ae57600080fd5b611a438761010060405190810160409081528254825260019092015467ffffffffffffffff8082166020840152680100000000000000008204169282019290925263ffffffff608060020a83048116606083015260a060020a83048116608083015260c060020a83041660a082015261ffff60e060020a8304811660c083015260f060020a90920490911660e0820152612b9c565b1515611a4e57600080fd5b60018701546006805460c060020a90920463ffffffff1697509087908110611a7257fe5b600091825260209091206001808a015460029093029091019081015490965061ffff60f060020a92839004811696509190041684901115611ac057600185015460f060020a900461ffff1693505b6010548754865460018a0154600160a060020a0390931692630d9f5aed92919068010000000000000000900467ffffffffffffffff166000190160006040516020015260405160e060020a63ffffffff86160281526004810193909352602483019190915267ffffffffffffffff166044820152606401602060405180830381600087803b1515611b5057600080fd5b6102c65a03f11515611b6157600080fd5b505050604051805160008b81526007602052604090205460018a810154929650600160a060020a039091169450611bb092508b9160c060020a900463ffffffff1690870161ffff1686866128f0565b6001880180547bffffffff00000000000000000000000000000000000000000000000019169055600f8054600019019055600e54909150600160a060020a0333169080156108fc0290604051600060405180830381858888f150939c9b505050505050505050505050565b60025433600160a060020a0390811691161480611c46575060005433600160a060020a039081169116145b80611c5f575060015433600160a060020a039081169116145b1515611c6a57600080fd5b600b54600160a060020a0316635fd8c7106040518163ffffffff1660e060020a028152600401600060405180830381600087803b1515611ca957600080fd5b6102c65a03f11515611cba57600080fd5b5050600c54600160a060020a03169050635fd8c7106040518163ffffffff1660e060020a028152600401600060405180830381600087803b1515611cfd57600080fd5b6102c65a03f11515610fdf57600080fd5b60408051908101604052600281527f434b000000000000000000000000000000000000000000000000000000000000602082015281565b600381600e8110611d5257fe5b60089182820401919006600402915054906101000a900463ffffffff1681565b600760205260009081526040902054600160a060020a031681565b60025460a060020a900460ff1615611da457600080fd5b600160a060020a0382161515611db957600080fd5b30600160a060020a031682600160a060020a031614151515611dda57600080fd5b600b54600160a060020a0383811691161415611df557600080fd5b600c54600160a060020a0383811691161415611e1057600080fd5b611e1a3382612572565b1515611e2557600080fd5b6116453383836125e0565b600254600160a060020a031681565b600e5481565b600d54600160a060020a031681565b60025460009033600160a060020a03908116911614611e7257600080fd5b60125461afc89010611e8357600080fd5b611e92600080600085306128f0565b600b54909150611eac908290600160a060020a0316612592565b600b54600160a060020a03166327ebe40a82611ec6612bd4565b6000620151803060405160e060020a63ffffffff88160281526004810195909552602485019390935260448401919091526064830152600160a060020a0316608482015260a401600060405180830381600087803b1515611f2657600080fd5b6102c65a03f11515611f3757600080fd5b5050601280546001019055505050565b600080808311611f5657600080fd5b6006805484908110611f6457fe5b906000526020600020906002020190506120098161010060405190810160409081528254825260019092015467ffffffffffffffff8082166020840152680100000000000000008204169282019290925263ffffffff608060020a83048116606083015260a060020a83048116608083015260c060020a83041660a082015261ffff60e060020a8304811660c083015260f060020a90920490911660e0820152612c82565b9392505050565b61138881565b60005433600160a060020a0390811691161461203157600080fd5b600d8054600160a060020a031916600160a060020a0392909216919091179055565b600b54600160a060020a031681565b600080600080600080600080600080600060068c81548110151561208257fe5b906000526020600020906002020190508060010160189054906101000a900463ffffffff1663ffffffff16600014159a50438160010160089054906101000a900467ffffffffffffffff1667ffffffffffffffff161115995080600101601c9054906101000a900461ffff1661ffff1698508060010160089054906101000a900467ffffffffffffffff1667ffffffffffffffff1697508060010160189054906101000a900463ffffffff1663ffffffff1696508060010160009054906101000a900467ffffffffffffffff1667ffffffffffffffff1695508060010160109054906101000a900463ffffffff1663ffffffff1694508060010160149054906101000a900463ffffffff1663ffffffff16935080600101601e9054906101000a900461ffff1661ffff16925080600001549150509193959799509193959799565b60025460009060a060020a900460ff16156121dd57600080fd5b6121e73383612572565b15156121f257600080fd5b6121fb82611f47565b151561220657600080fd5b6122108284612cb9565b151561221b57600080fd5b600c54600160a060020a031663c55d0f568460006040516020015260405160e060020a63ffffffff84160281526004810191909152602401602060405180830381600087803b151561226c57600080fd5b6102c65a03f1151561227d57600080fd5b5050506040518051600e549092508201341015905061229b57600080fd5b600c54600e54600160a060020a039091169063454a2ab39034038560405160e060020a63ffffffff851602815260048101919091526024016000604051808303818588803b15156122eb57600080fd5b6125ee5a03f115156122fc57600080fd5b50505050610fdf8263ffffffff168463ffffffff16612d08565b60125481565b601054600160a060020a031681565b600254600090819060a060020a900460ff161561234757600080fd5b600e5434101561235657600080fd5b6123603385612572565b151561236b57600080fd5b612375838561289b565b151561238057600080fd5b600680548590811061238e57fe5b906000526020600020906002020191506124338261010060405190810160409081528254825260019092015467ffffffffffffffff8082166020840152680100000000000000008204169282019290925263ffffffff608060020a83048116606083015260a060020a83048116608083015260c060020a83041660a082015261ffff60e060020a8304811660c083015260f060020a90920490911660e0820152612c82565b151561243e57600080fd5b600680548490811061244c57fe5b906000526020600020906002020190506124f18161010060405190810160409081528254825260019092015467ffffffffffffffff8082166020840152680100000000000000008204169282019290925263ffffffff608060020a83048116606083015260a060020a83048116608083015260c060020a83041660a082015261ffff60e060020a8304811660c083015260f060020a90920490911660e0820152612c82565b15156124fc57600080fd5b6125088285838661271b565b151561251357600080fd5b61155a8484612d08565b612525612fa0565b61252d612fa0565b6000808460405180591061253e5750595b818152601f19601f8301168101602001604052905092505060208201905084612568828287612e72565b5090949350505050565b600090815260076020526040902054600160a060020a0391821691161490565b6000918252600960205260409091208054600160a060020a031916600160a060020a03909216919091179055565b600090815260096020526040902054600160a060020a0391821691161490565b600160a060020a03808316600081815260086020908152604080832080546001019055858352600790915290208054600160a060020a031916909117905583161561267357600160a060020a03831660009081526008602090815260408083208054600019019055838352600a82528083208054600160a060020a03199081169091556009909252909120805490911690555b7fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef838383604051600160a060020a039384168152919092166020820152604080820192909252606001905180910390a1505050565b60005433600160a060020a039081169116146126e357600080fd5b60025460a060020a900460ff1615156126fb57600080fd5b6002805474ff000000000000000000000000000000000000000019169055565b60008184141561272d57506000612893565b6001850154608060020a900463ffffffff1682148061275c5750600185015460a060020a900463ffffffff1682145b1561276957506000612893565b6001830154608060020a900463ffffffff168414806127985750600183015460a060020a900463ffffffff1684145b156127a557506000612893565b6001830154608060020a900463ffffffff1615806127d257506001850154608060020a900463ffffffff16155b156127df57506001612893565b60018581015490840154608060020a9182900463ffffffff9081169290910416148061282a575060018086015490840154608060020a900463ffffffff90811660a060020a90920416145b1561283757506000612893565b6001808601549084015460a060020a900463ffffffff908116608060020a90920416148061288257506001858101549084015460a060020a9182900463ffffffff9081169290910416145b1561288f57506000612893565b5060015b949350505050565b6000818152600760205260408082205484835290822054600160a060020a0391821691168082148061133e57506000858152600a6020526040902054600160a060020a03908116908316149250505092915050565b6000806128fb612fdb565b600063ffffffff8916891461290f57600080fd5b63ffffffff8816881461292157600080fd5b61ffff8716871461293157600080fd5b600287049250600d8361ffff16111561294957600d92505b610100604051908101604090815287825267ffffffffffffffff42166020830152600090820181905263ffffffff808c1660608401528a16608083015260a082015261ffff80851660c0830152881660e0820152600680549193506001918083016129b4838261301f565b6000928352602090922085916002020181518155602082015160018201805467ffffffffffffffff191667ffffffffffffffff9290921691909117905560408201518160010160086101000a81548167ffffffffffffffff021916908367ffffffffffffffff16021790555060608201518160010160106101000a81548163ffffffff021916908363ffffffff16021790555060808201518160010160146101000a81548163ffffffff021916908363ffffffff16021790555060a08201518160010160186101000a81548163ffffffff021916908363ffffffff16021790555060c082015181600101601c6101000a81548161ffff021916908361ffff16021790555060e08201516001909101805461ffff9290921660f060020a027dffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9092169190911790555003905063ffffffff81168114612b0f57600080fd5b7f0a5311bd2a6608f08a180df2ee7c5946819a649b204b554bb8e39825b2c50ad58582846060015163ffffffff16856080015163ffffffff168651604051600160a060020a03909516855260208501939093526040808501929092526060840152608083019190915260a0909101905180910390a1612b90600086836125e0565b98975050505050505050565b60008160a0015163ffffffff1615801590610c6f57504367ffffffffffffffff16826040015167ffffffffffffffff16111592915050565b600b5460009081908190600160a060020a031663eac9d94c82604051602001526040518163ffffffff1660e060020a028152600401602060405180830381600087803b1515612c2257600080fd5b6102c65a03f11515612c3357600080fd5b50505060405180519250506fffffffffffffffffffffffffffffffff82168214612c5c57600080fd5b50600281048101662386f26fc10000811015612c7c5750662386f26fc100005b92915050565b60008160a0015163ffffffff16158015610c6f57504367ffffffffffffffff16826040015167ffffffffffffffff16111592915050565b6000806000600685815481101515612ccd57fe5b90600052602060002090600202019150600684815481101515612cec57fe5b9060005260206000209060020201905061133e8286838761271b565b600080600683815481101515612d1a57fe5b90600052602060002090600202019150600684815481101515612d3957fe5b600091825260209091206002909102016001810180547bffffffff000000000000000000000000000000000000000000000000191660c060020a63ffffffff8716021790559050612d8982612eb7565b612d9281612eb7565b6000848152600a602090815260408083208054600160a060020a031990811690915586845281842080549091169055600f8054600190810190915587845260079092529182902054908301547f241ea03ca20251805084d27d4440371c34a0b85ff108f6bb5611248f73818b8092600160a060020a0390921691879187916801000000000000000090910467ffffffffffffffff1690518085600160a060020a0316600160a060020a031681526020018481526020018381526020018267ffffffffffffffff16815260200194505050505060405180910390a150505050565b60005b60208210612e985782518452602084019350602083019250602082039150612e75565b6001826020036101000a03905080198351168185511617909352505050565b600554600182015443919060039060e060020a900461ffff16600e8110612eda57fe5b600891828204019190066004029054906101000a900463ffffffff1663ffffffff16811515612f0557fe5b6001840180546fffffffffffffffff0000000000000000191668010000000000000000939092049390930167ffffffffffffffff16919091021790819055600d60e060020a90910461ffff161015612f9d576001818101805461ffff60e060020a8083048216909401169092027fffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff9092169190911790555b50565b60206040519081016040526000815290565b60806040519081016040526004815b60008152600019919091019060200181612fc15790505090565b6101006040519081016040908152600080835260208301819052908201819052606082018190526080820181905260a0820181905260c0820181905260e082015290565b815481835581811511610fdf57600083815260209020610fdf91610ef99160029182028101918502015b808211156130635760008082556001820155600201613049565b50905600a165627a7a72305820a6465fc1ce7ab1a92906ff7206b23d80a21bbd50b85b4bde6a91f8e6b2e3edde0029";
    let analyzer = common::new_analyzer_from_bytecode(bytecode, LazyWatchdog.in_rc())?;

    // Get the final storage layout for the input contract
    let layout = analyzer.analyze()?;

    // We should see 21 entries, but we actually only see 20 due to missing features
    assert_eq!(layout.slots().len(), 20);

    // `address`, but we infer `number160`
    assert!(
        layout
            .slots()
            .contains(&StorageSlot::new(0, 0, AbiType::Number { size: Some(160) }))
    );

    // `address`
    assert!(layout.slots().contains(&StorageSlot::new(1, 0, AbiType::Address)));

    // `address`
    assert!(layout.slots().contains(&StorageSlot::new(2, 0, AbiType::Address)));

    // `uint32[14]`, but we infer `uint32`
    assert!(
        layout
            .slots()
            .contains(&StorageSlot::new(3, 0, AbiType::UInt { size: Some(32) }))
    );

    // We don't see the rest of that array slot for now.
    assert!(!layout.slots().iter().any(|s| s.offset == 4));

    // `uint256`
    assert!(
        layout
            .slots()
            .contains(&StorageSlot::new(5, 0, AbiType::UInt { size: Some(256) }))
    );

    // `struct[]` but we infer `bytes32[]`
    assert!(layout.slots().contains(&StorageSlot::new(
        6,
        0,
        AbiType::DynArray {
            tp: Box::new(AbiType::Bytes { length: Some(32) }),
        }
    )));

    // `mapping(uint256 => address)` but we infer `mapping(uint32 => address)`
    assert!(layout.slots().contains(&StorageSlot::new(
        7,
        0,
        AbiType::Mapping {
            key_type:   Box::new(AbiType::UInt { size: Some(32) }),
            value_type: Box::new(AbiType::Address),
        }
    )));

    // `mapping(address => uint256)` but we infer `mapping(address => uintUnknown)`
    assert!(layout.slots().contains(&StorageSlot::new(
        8,
        0,
        AbiType::Mapping {
            key_type:   Box::new(AbiType::Address),
            value_type: Box::new(AbiType::UInt { size: None }),
        }
    )));

    // `mapping(uint256 => address)` but we infer `mapping(uint32 => address)`
    assert!(layout.slots().contains(&StorageSlot::new(
        9,
        0,
        AbiType::Mapping {
            key_type:   Box::new(AbiType::UInt { size: Some(32) }),
            value_type: Box::new(AbiType::Address),
        }
    )));

    // `mapping(uint256 => address)` but we infer `mapping(uint32 => bytes20)`
    assert!(layout.slots().contains(&StorageSlot::new(
        10,
        0,
        AbiType::Mapping {
            key_type:   Box::new(AbiType::UInt { size: Some(32) }),
            value_type: Box::new(AbiType::Bytes { length: Some(20) }),
        }
    )));

    // `address`
    assert!(layout.slots().contains(&StorageSlot::new(11, 0, AbiType::Address)));

    // `address`
    assert!(layout.slots().contains(&StorageSlot::new(12, 0, AbiType::Address)));

    // `address`
    assert!(layout.slots().contains(&StorageSlot::new(13, 0, AbiType::Address)));

    // `uint256` but we infer `uint256`
    assert!(
        layout
            .slots()
            .contains(&StorageSlot::new(14, 0, AbiType::UInt { size: Some(256) }))
    );

    // `uint256` but we infer `numberUnknown`
    assert!(
        layout
            .slots()
            .contains(&StorageSlot::new(15, 0, AbiType::Number { size: None }))
    );

    // `address`
    assert!(layout.slots().contains(&StorageSlot::new(16, 0, AbiType::Address)));

    // `uint256` but we infer `uintUnknown`
    assert!(
        layout
            .slots()
            .contains(&StorageSlot::new(17, 0, AbiType::UInt { size: None }))
    );

    // `uint256` but we infer `uintUnknown`
    assert!(
        layout
            .slots()
            .contains(&StorageSlot::new(18, 0, AbiType::UInt { size: None }))
    );

    // `address` but we infer `bytes20`
    assert!(layout.slots().contains(&StorageSlot::new(
        19,
        0,
        AbiType::Number { size: Some(160) }
    )));

    Ok(())
}
