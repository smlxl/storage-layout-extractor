//! This module tests the library's analysis capabilities on the `EnsoWallet`
//! contract`.
#![cfg(test)]

use std::str::FromStr;

use ethnum::U256;
use storage_layout_extractor::{tc::abi::AbiType, watchdog::LazyWatchdog};

mod common;

/// Tests the library on the bytecode of the EnsoWallet contract deployed
/// [here](https://etherscan.io/address/0x498d5a77e1b7f508af018f5bcd286134ea91179c).
#[test]
fn correctly_generates_a_layout() -> anyhow::Result<()> {
    // Create the extractor
    let bytecode = "0x6080604052600436101561001b575b361561001957600080fd5b005b60003560e01c806301ffc9a7146101ca57806307bd0265146101c15780630fe786e114610131578063150b7a02146101b85780631626ba7e146101af57806320c13b0b146101a657806331b455a51461019d57806356255c5314610194578063599e4c701461018b57806360d6c7cf146101825780638a2685a914610179578063a4508b1f14610170578063b61d27f614610167578063bc197c811461015e578063d27b979514610155578063dedd65241461014c578063e1084a1314610143578063e58378bb1461013a578063e5cb370314610131578063f14210a614610128578063f23a6e611461011f5763fdb09f3c0361000e5761011a6113ae565b61000e565b5061011a611237565b5061011a6111ed565b5061011a610487565b5061011a611193565b5061011a611064565b5061011a610f10565b5061011a610e0a565b5061011a610d14565b5061011a610c91565b5061011a610c02565b5061011a610b37565b5061011a610ae3565b5061011a6109fb565b5061011a61097d565b5061011a6108ab565b5061011a610730565b5061011a610646565b5061011a6105b5565b5061011a61029a565b503461028a5760207ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576004357fffffffff00000000000000000000000000000000000000000000000000000000811680910361028a57807f4e2312e00000000000000000000000000000000000000000000000000000000060209214908115610260575b506040519015158152f35b7f01ffc9a70000000000000000000000000000000000000000000000000000000091501438610255565b600080fd5b600091031261028a57565b503461028a5760007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a5760206040517fd931ed5eea9427443091b211e417e6f83bd1d1a5235f4e7adbb05b55612080308152f35b73ffffffffffffffffffffffffffffffffffffffff81160361028a57565b507f4e487b7100000000000000000000000000000000000000000000000000000000600052604160045260246000fd5b6080810190811067ffffffffffffffff82111761035e57604052565b610366610312565b604052565b6060810190811067ffffffffffffffff82111761035e57604052565b67ffffffffffffffff811161035e57604052565b6040810190811067ffffffffffffffff82111761035e57604052565b90601f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0910116810190811067ffffffffffffffff82111761035e57604052565b60209067ffffffffffffffff8111610412575b60051b0190565b61041a610312565b61040b565b81601f8201121561028a57803591610436836103f8565b9261044460405194856103b7565b808452602092838086019260051b82010192831161028a578301905b82821061046e575050505090565b838091833561047c816102f4565b815201910190610460565b503461028a5760407ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576004356104c3816102f4565b60243567ffffffffffffffff811161028a576104e390369060040161041f565b6104ec336125a0565b54156104fb5761001991613585565b60046040517f39218f3b000000000000000000000000000000000000000000000000000000008152fd5b7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0601f60209267ffffffffffffffff8111610561575b01160190565b610569610312565b61055b565b81601f8201121561028a5780359061058582610525565b9261059360405194856103b7565b8284526020838301011161028a57816000926020809301838601378301015290565b503461028a5760807ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576105f06004356102f4565b6105fb6024356102f4565b60643567ffffffffffffffff811161028a5761061b90369060040161056e565b5060206040517f150b7a02000000000000000000000000000000000000000000000000000000008152f35b503461028a5760407ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a5760243567ffffffffffffffff811161028a576106af6106a761069f6106b493369060040161056e565b600435612a4e565b91909161282f565b6125a0565b54156107085760207f1626ba7e000000000000000000000000000000000000000000000000000000005b7fffffffff0000000000000000000000000000000000000000000000000000000060405191168152f35b60207fffffffff000000000000000000000000000000000000000000000000000000006106de565b503461028a5760407ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a5767ffffffffffffffff60043581811161028a5761078190369060040161056e565b60243591821161028a576106a76106af916107a361082094369060040161056e565b906107ae8151612b75565b90610818603a604051809360208201957f19457468657265756d205369676e6564204d6573736167653a0a00000000000087526107f481518092602087870191016112c8565b820161080982518093602087850191016112c8565b0103601a8101845201826103b7565b519020612a4e565b54156108825761087e7f20c13b0b000000000000000000000000000000000000000000000000000000005b6040517fffffffff0000000000000000000000000000000000000000000000000000000090911681529081906020820190565b0390f35b61087e7fffffffff0000000000000000000000000000000000000000000000000000000061084b565b503461028a5760407ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576004356108e7816102f4565b60243567ffffffffffffffff811161028a5761090790369060040161041f565b610910336125a0565b54156104fb57610019916134e0565b81601f8201121561028a57803591610936836103f8565b9261094460405194856103b7565b808452602092838086019260051b82010192831161028a578301905b82821061096e575050505090565b81358152908301908301610960565b503461028a5760407ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576004356109b9816102f4565b60243567ffffffffffffffff811161028a576109d990369060040161091f565b6109e2336125a0565b54156104fb5761001991613310565b8015150361028a57565b503461028a5760607ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a57600435602435610a3a816102f4565b60443590610a47826109f1565b610a50336125a0565b54156104fb577f3fbe42dcb277543d3741131fe04ce9fb205e3b7154603a23a25efd63ed2c9e1c831480610ac4575b80610abc575b610a925761001992612791565b60046040517f337b9b30000000000000000000000000000000000000000000000000000000008152fd5b508115610a85565b503373ffffffffffffffffffffffffffffffffffffffff821614610a7f565b503461028a5760407ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576020610b2c602435610b24816102f4565b60043561264c565b546040519015158152f35b503461028a5760407ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a5767ffffffffffffffff60043581811161028a573660238201121561028a578060040135610b93816103f8565b91610ba160405193846103b7565b81835260209160248385019160051b8301019136831161028a57602401905b828210610be9576024358587821161028a57610be361001992369060040161091f565b90612ea9565b8380918335610bf7816102f4565b815201910190610bc0565b503461028a5760607ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a57600435610c3e816102f4565b67ffffffffffffffff60243581811161028a57610c5f90369060040161091f565b9060443590811161028a57610c7890369060040161091f565b90610c82336125a0565b54156104fb5761001992613402565b5060607ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a57600435610cc8816102f4565b60443567ffffffffffffffff811161028a57610ce890369060040161056e565b610cf1336125f9565b54156104fb5760008160209384839451920190602435905af16040519015158152f35b503461028a5760a07ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a57610d4f6004356102f4565b610d5a6024356102f4565b67ffffffffffffffff60443581811161028a57610d7b90369060040161091f565b5060643581811161028a57610d9490369060040161091f565b5060843590811161028a57610dad90369060040161056e565b506040517fbc197c81000000000000000000000000000000000000000000000000000000008152602090f35b9181601f8401121561028a5782359167ffffffffffffffff831161028a576020808501948460051b01011161028a57565b5060807ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a57600435610e41816102f4565b67ffffffffffffffff60443581811161028a57610e62903690600401610dd9565b909160643590811161028a57610e7c903690600401610dd9565b90937f8ace5aef1887be9219d1b04dbcfb5676ed5a12ec4a1129de5781d4d7ea71c9ed908154610ed957610ebd916024359055610eb881612680565b612715565b81610ec457005b61001993610ed39136916114d8565b9161166a565b60046040517fef34ca5c000000000000000000000000000000000000000000000000000000008152fd5b3590600482101561028a57565b503461028a576020807ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576004359067ffffffffffffffff9081831161028a573660238401121561028a57826004013592610f70846103f8565b93604093610f80855196876103b7565b818652838601906024809360051b8501019336851161028a57838101925b858410610fb457600088610fb18b612c81565b51f35b833583811161028a57820160807fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc823603011261028a57885191610ff783610342565b611002878301610f03565b83526044820135611012816102f4565b89840152606482013585811161028a576110319088369185010161091f565b8a84015260848201359285841161028a576110548a94938986953692010161091f565b6060820152815201930192610f9e565b503461028a576020807ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576004359067ffffffffffffffff80831161028a573660238401121561028a578260040135916110c3836103f8565b916040936110d3855194856103b7565b8084528284016024809260051b8801019236841161028a57828801915b84831061110357600088610fb189612f0b565b823582811161028a57890160607fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc823603011261028a578851916111468361036b565b611151868301610f03565b83526044820135611161816102f4565b8884015260648201359284841161028a576111848994938886953692010161041f565b8b8201528152019201916110f0565b503461028a5760007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a5760206040517f3fbe42dcb277543d3741131fe04ce9fb205e3b7154603a23a25efd63ed2c9e1c8152f35b503461028a5760207ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a57611226336125a0565b54156104fb5761001960043561306c565b503461028a5760a07ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a576112726004356102f4565b61127d6024356102f4565b60843567ffffffffffffffff811161028a5761129d90369060040161056e565b5060206040517ff23a6e61000000000000000000000000000000000000000000000000000000008152f35b60005b8381106112db5750506000910152565b81810151838201526020016112cb565b907fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0601f602093611327815180928187528780880191016112c8565b0116010190565b602080820190808352835180925260408301928160408460051b8301019501936000915b8483106113625750505050505090565b909192939495848061139e837fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc086600196030187528a516112eb565b9801930193019194939290611352565b5060407ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc36011261028a5767ffffffffffffffff60043581811161028a576113fa903690600401610dd9565b909160243590811161028a57611414903690600401610dd9565b929091611420336125f9565b54156104fb57610ed36114389361087e9536916114d8565b6040519182918261132e565b507f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b907fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff82019182116114a157565b6114a9611444565b565b907fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe082019182116114a157565b929190926114e5846103f8565b916114f360405193846103b7565b829480845260208094019060051b83019282841161028a5780915b84831061151d57505050505050565b823567ffffffffffffffff811161028a57869161153d868493860161056e565b81520192019161150e565b507f4e487b7100000000000000000000000000000000000000000000000000000000600052603260045260246000fd5b91908110156115885760051b0190565b61041a611548565b60209080511561159e570190565b6115a6611548565b0190565b60209181518110156115bf575b60051b010190565b6115c7611548565b6115b7565b3d156115f7573d906115dd82610525565b916115eb60405193846103b7565b82523d6000602084013e565b606090565b604051906116098261039b565b600782527f556e6b6e6f776e000000000000000000000000000000000000000000000000006020830152565b73ffffffffffffffffffffffffffffffffffffffff6116679493606093835216602082015281604082015201906112eb565b90565b9060005b81811061167b5750505090565b611686818385611578565b604091903560d881901c838116159283611a5657600101936116a9858789611578565b355b60038381168061184a57505060008091602090818616158314611833576116f5907fffffffff0000000000000000000000000000000000000000000000000000000088168d611b15565b905b8151910173ffffffffffffffffffffffffffffffffffffffff87165af49361171d6115cc565b945b156117a15750506080161561176757600192917fff000000000000000000000000000000000000000000000000000000000000006117619260581b1687612520565b0161166e565b90600192957fff0000000000000000000000000000000000000000000000000000000000000061179b9360581b1690612474565b93611761565b6118079250938573ffffffffffffffffffffffffffffffffffffffff958251611829575b1561181a57905b80511561180b57915b519485947fef3dcb2f000000000000000000000000000000000000000000000000000000008652169060048501611635565b0390fd5b506118146115fc565b916117d5565b61182390611474565b906117cc565b91604401916117c5565b607f6118439160f81c168c6115aa565b51906116f7565b600181036118d8575050600080916020908186161583146118c157611892907fffffffff0000000000000000000000000000000000000000000000000000000088168d611b15565b905b815191018273ffffffffffffffffffffffffffffffffffffffff88165af1936118bb6115cc565b9461171f565b607f6118d19160f81c168c6115aa565b5190611894565b6002810361195f5750506000809160209081861615831461194857611920907fffffffff0000000000000000000000000000000000000000000000000000000088168d611b15565b905b8151910173ffffffffffffffffffffffffffffffffffffffff87165afa936118bb6115cc565b607f6119589160f81c168c6115aa565b5190611922565b036119f857600080916020908161197a8d8360f81c906115aa565b510151908287161584146119e1576119b89060081b7fffffffff0000000000000000000000000000000000000000000000000000000089168e611b15565b915b825192019073ffffffffffffffffffffffffffffffffffffffff88165af1936118bb6115cc565b607f6119f19160f01c168d6115aa565b51916119ba565b50517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601060248201527f496e76616c69642063616c6c74797065000000000000000000000000000000006044820152606490fd5b9379ffffffffffffffffffffffffffffffffffffffffffffffffffff8360281b176116ab565b60405190610160820182811067ffffffffffffffff821117611aab575b604052600a8252610140366020840137565b611ab3610312565b611a99565b90600482018092116114a157565b90611ad082610525565b611add60405191826103b7565b8281527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0611b0b8294610525565b0190602036910137565b929192600090818291611b26611a7c565b916060928596865b60209081891015611dc1578b891a60ff8114611c30576080811615611c225760fe8103611bbe5750865115611b71575b90600191875101975b0197019695611b2e565b9550600190604051611bb581611b898985830161132e565b037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe081018352826103b7565b96909150611b5e565b92989197949193909260fd8103611bef5750916001949391611be1938d88611f1b565b989294919790979493611b67565b60fc8103611c095750916001949391611be1938d88611fc6565b611c1c90600193969992959a9488611e78565b97611b67565b611c1c906001939288611dd6565b5097985090969194939250611c4e91611c499150611ab8565b611ac6565b97602095868a0152600093849185965b898810611c715750505050505050505050565b889081891015611db4575b8c838a1a6080811615611d8f5760fe8103611ced575081611cdd826001959460248d7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe096010152611ccc83611ab8565b611cd68c516114ab565b918c61258e565b885101019701975b019695611c5e565b929895919260fd8103611d2357509160019991858589868560248c611d149a0101526120c3565b90509891979097940197611ce5565b60fc8103611d4557509160019991858589868560248c611d149a010152612114565b92611d8687602493611d758b859b9e979b611d66607f60019b1680936115aa565b5151978895850101528c6115aa565b5190611d8085611ab8565b9161257c565b01970197611ce5565b9060248a85611da6607f600198979e96168c6115aa565b510151920101520197611ce5565b611dbc611548565b611c7c565b9050611c49919750611c4e9295949350611ab8565b611de790607f6020939416906115aa565b515103611df45760200190565b60846040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602760248201527f537461746963207374617465207661726961626c6573206d757374206265203360448201527f32206279746573000000000000000000000000000000000000000000000000006064820152fd5b607f611e86929316906115aa565b5151601f8116611e97570160200190565b60846040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152603660248201527f44796e616d6963207374617465207661726961626c6573206d7573742062652060448201527f61206d756c7469706c65206f66203332206279746573000000000000000000006064820152fd5b9291909394600101936020851015611fb9575b6020611f3f607f83881a16866115aa565b515103611f5b576020611f53960193611fc6565b929391929091565b60646040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601d60248201527f4172726179206c656e677468206d7573742062652033322062797465730000006044820152fd5b611fc1611548565b611f2e565b9493909592600091600180960195808301986020809301985b838910611ff25750505050505093929190565b81891a60808116156120b05760fb810361201c57505050505061201590836115aa565b5293929190565b9a849b978860fd869d949697999a9c959c1460001461205c5750906120449392918b86611f1b565b9b929b9a919a96909a9b975b01950197909291611fdf565b60fc9193959798508092949650146000146120945750928492612084928b958b8e9998611fc6565b9b929b9a919a96909a9b97612050565b9a6120aa81939c87958d9799989d949a9d611e78565b9a612050565b936120aa849582949b989c849694611dd6565b93929190602060016120fb98019681881015612107575b816120ea607f868b1a16856115aa565b510151602482890101520194612114565b92939192602090910191565b61210f611548565b6120da565b949095929196939660009661212989856115aa565b51906001808584019b019601975b602095868a101561228057848a1a60808116156122515760fb810361216457505050505050505093929190565b9b8498889d958660fd8a9f9b989e9596979a999e146000146121b8575060248697986121979697010152848c89886120c3565b919c9781019095019a91979094019501926001905b01979293909491612137565b92949650509193955060fc81146000146122005750916121e7918594938960248f988f010152848c8988612114565b919c9781019095019a91979094019501926001906121ac565b9b8860248d83949b9f956122438a6122388d607f60019b9e9d9c9e169061222782826115aa565b5151988998899889960101526115aa565b518b611d8085611ab8565b019e019801019a01936121ac565b96869b8192949760248361226f999e99607f6001989a9d168c6115aa565b5101519188010152019a01936121ac565b5050505050505093929190565b1561229457565b60846040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602860248201527f4f6e6c79206f6e652072657475726e2076616c7565207065726d69747465642060448201527f28737461746963290000000000000000000000000000000000000000000000006064820152fd5b1561231f57565b60846040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602a60248201527f4f6e6c79206f6e652072657475726e2076616c7565207065726d69747465642060448201527f287661726961626c6529000000000000000000000000000000000000000000006064820152fd5b602090818184031261028a57805167ffffffffffffffff9182821161028a57019083601f8301121561028a5781516123da816103f8565b946040926123ea845197886103b7565b828752858088019360051b8601019482861161028a57868101935b86851061241757505050505050505090565b845183811161028a5782019084603f8301121561028a57888201519061243c82610525565b612448895191826103b7565b8281528689848601011161028a576124698b949385948b86850191016112c8565b815201940193612405565b91908060f81c60ff811461251a5760808116156124ed5760fe036124a757506116679150602080825183010191016123a3565b610fe06020917fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0838501946124de85875114612318565b5101845260f31c168301015290565b829150607f90612503602061251695511461228d565b169061250f82856115aa565b52826115aa565b5090565b50505090565b9060f81c9060ff82146125775760209161255891612548855185810180911161256f57611ac6565b61255283836115aa565b526115aa565b51918051604084018184840160045afa5051910152565b611c49611444565b505050565b916020809185930101920160045afa50565b910160200190829060400160045afa50565b60405173ffffffffffffffffffffffffffffffffffffffff60208201927f3fbe42dcb277543d3741131fe04ce9fb205e3b7154603a23a25efd63ed2c9e1c8452166040820152604081526125f38161036b565b51902090565b60405173ffffffffffffffffffffffffffffffffffffffff60208201927fd931ed5eea9427443091b211e417e6f83bd1d1a5235f4e7adbb05b55612080308452166040820152604081526125f38161036b565b9073ffffffffffffffffffffffffffffffffffffffff6040519160208301938452166040820152604081526125f38161036b565b60607ff7682c7604ab581823c6ee4b22f8283179771e57c8115328f4a698be07430a419160405160016020820173ffffffffffffffffffffffffffffffffffffffff7f3fbe42dcb277543d3741131fe04ce9fb205e3b7154603a23a25efd63ed2c9e1c948583521692836040820152604081526126fc8161036b565b51902055604051918252602082015260016040820152a1565b60607ff7682c7604ab581823c6ee4b22f8283179771e57c8115328f4a698be07430a419160405160016020820173ffffffffffffffffffffffffffffffffffffffff7fd931ed5eea9427443091b211e417e6f83bd1d1a5235f4e7adbb05b5561208030948583521692836040820152604081526126fc8161036b565b7ff7682c7604ab581823c6ee4b22f8283179771e57c8115328f4a698be07430a419273ffffffffffffffffffffffffffffffffffffffff606093826127d6828661264c565b5560405193845216602083015215156040820152a1565b507f4e487b7100000000000000000000000000000000000000000000000000000000600052602160045260246000fd5b6005111561282757565b6114a96127ed565b6128388161281d565b806128405750565b6128498161281d565b600181036128b0576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601860248201527f45434453413a20696e76616c6964207369676e617475726500000000000000006044820152606490fd5b6128b98161281d565b60028103612920576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601f60248201527f45434453413a20696e76616c6964207369676e6174757265206c656e677468006044820152606490fd5b6129298161281d565b600381036129b6576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602260248201527f45434453413a20696e76616c6964207369676e6174757265202773272076616c60448201527f75650000000000000000000000000000000000000000000000000000000000006064820152608490fd5b806129c260049261281d565b146129c957565b6040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602260248201527f45434453413a20696e76616c6964207369676e6174757265202776272076616c60448201527f75650000000000000000000000000000000000000000000000000000000000006064820152608490fd5b906041815114600014612a7c57612a78916020820151906060604084015193015160001a90612a93565b9091565b5050600090600290565b506040513d6000823e3d90fd5b9291907f7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a08311612b4a5760ff16601b81141580612b3f575b612b33579160809493916020936040519384528484015260408301526060820152600093849182805260015afa15612b26575b815173ffffffffffffffffffffffffffffffffffffffff811615612b20579190565b50600190565b612b2e612a86565b612afe565b50505050600090600490565b50601c811415612acb565b50505050600090600390565b906020918051821015612b6857010190565b612b70611548565b010190565b8015612c47576000818181805b612bff5750612b9081611ac6565b935b612b9c5750505090565b612ba590611474565b90600a907fff0000000000000000000000000000000000000000000000000000000000000060308383068101809111612bf2575b60f81b16841a612be98487612b56565b53049081612b92565b612bfa611444565b612bd9565b91506001817fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600a9314612c3a575b01910480849291612b82565b612c42611444565b612c2e565b50604051612c548161039b565b600181527f3000000000000000000000000000000000000000000000000000000000000000602082015290565b612c8a336125a0565b54156104fb57612c98612e5a565b5080519060005b828110612cab57505050565b612cb581836115aa565b5190815191612cc383612e9f565b612ccc83612e9f565b82612d44576060015180519092507fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01612d1a57612d14612d0e600193611590565b5161306c565b01612c9f565b60046040517f9d89020a000000000000000000000000000000000000000000000000000000008152fd5b612d4d83612e9f565b600192808403612dbd5750606081015192835103612d1a57600192612db1612dab612d926020612db895015173ffffffffffffffffffffffffffffffffffffffff1690565b73ffffffffffffffffffffffffffffffffffffffff1690565b91611590565b51906130b2565b612d14565b60019350612dca81612e9f565b60028103612e05575080612e00612d9260206040612db895015193015173ffffffffffffffffffffffffffffffffffffffff1690565b613310565b80612e11600392612e9f565b14612e1d575b50612d14565b806040612e54920151612e4f612d926020606085015194015173ffffffffffffffffffffffffffffffffffffffff1690565b613402565b38612e17565b604051906080820182811067ffffffffffffffff821117612e92575b6040526060808360008152600060208201528160408201520152565b612e9a610312565b612e76565b6004111561282757565b90612eb3336125a0565b54156104fb5781519182825103612d1a5760005b838110612ed45750505050565b80612f0573ffffffffffffffffffffffffffffffffffffffff612ef9600194866115aa565b5116612db183876115aa565b01612ec7565b612f14336125a0565b54156104fb57612f2261302c565b5080519060005b828110612f3557505050565b612f3f81836115aa565b5190815191612f4d83612e9f565b612f5683612e9f565b600192808403612f9a5750806040612f8b612d926020612f9495015173ffffffffffffffffffffffffffffffffffffffff1690565b910151906134e0565b01612f29565b612fa381612e9f565b60028103612fe45750806040612fd6612d926020612fdf95015173ffffffffffffffffffffffffffffffffffffffff1690565b91015190613585565b612f94565b80612ff0600392612e9f565b14612ffc575b50612f94565b806040612fd6612d92602061302695015173ffffffffffffffffffffffffffffffffffffffff1690565b38612ff6565b604051906060820182811067ffffffffffffffff82111761305f575b604052606060408360008152600060208201520152565b613067610312565b613048565b600080809260405190335af16130806115cc565b501561308857565b60046040517f750b219c000000000000000000000000000000000000000000000000000000008152fd5b906114a991604051917fa9059cbb0000000000000000000000000000000000000000000000000000000060208401523360248401526044830152604482526080820182811067ffffffffffffffff821117613110575b6040526131bd565b613118610312565b613108565b9081602091031261028a5751611667816109f1565b1561313957565b60846040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602a60248201527f5361666545524332303a204552433230206f7065726174696f6e20646964206e60448201527f6f742073756363656564000000000000000000000000000000000000000000006064820152fd5b73ffffffffffffffffffffffffffffffffffffffff1690604051906131e18261039b565b6020928383527f5361666545524332303a206c6f772d6c6576656c2063616c6c206661696c656484840152803b1561325857600082819282876132339796519301915af161322d6115cc565b906132b6565b8051908161324057505050565b826114a99361325393830101910161311d565b613132565b606484604051907f08c379a00000000000000000000000000000000000000000000000000000000082526004820152601d60248201527f416464726573733a2063616c6c20746f206e6f6e2d636f6e74726163740000006044820152fd5b909190156132c2575090565b8151156132d25750805190602001fd5b611807906040519182917f08c379a00000000000000000000000000000000000000000000000000000000083526020600484015260248301906112eb565b81519060005b8281106133235750505050565b73ffffffffffffffffffffffffffffffffffffffff82169061334581866115aa565b5191803b1561028a5760008091606460019560405194859384927f42842e0e00000000000000000000000000000000000000000000000000000000845230600485015233602485015260448401525af180156133c1575b6133a8575b5001613316565b806133b56133bb92610387565b8061028f565b386133a1565b6133c9612a86565b61339c565b90815180825260208080930193019160005b8281106133ee575050505090565b8351855293810193928101926001016133e0565b73ffffffffffffffffffffffffffffffffffffffff1691823b1561028a576134a892600092836020613477948260405198899788967f2eb2c2d600000000000000000000000000000000000000000000000000000000885230600489015233602489015260a0604489015260a48801906133ce565b7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc93848883030160648901526133ce565b85810392830160848701525201925af180156134d3575b6134c65750565b806133b56114a992610387565b6134db612a86565b6134bf565b81519160005b8381106134f35750505050565b8061357f611b8961357973ffffffffffffffffffffffffffffffffffffffff61351e600196886115aa565b51166040519283917f095ea7b300000000000000000000000000000000000000000000000000000000602084015260248301602060009193929373ffffffffffffffffffffffffffffffffffffffff60408201951681520152565b856131bd565b016134e6565b81519060005b8281106135985750505050565b73ffffffffffffffffffffffffffffffffffffffff90818316916135bc82876115aa565b5116823b1561028a576040517fa22cb46500000000000000000000000000000000000000000000000000000000815273ffffffffffffffffffffffffffffffffffffffff9190911660048201526000602482018190526001938290604490829084905af18015613642575b613633575b500161358b565b61363c90610387565b3861362c565b61364a612a86565b61362756fea2646970667358221220cd41ba60fd8b598e36bc8ae136278bbd22b61ec813b02da52384cf209b62dac564736f6c63430008100033";
    let extractor = common::new_extractor_from_bytecode(bytecode, LazyWatchdog.in_rc())?;

    // Get the final storage layout for the input contract
    let layout = extractor.analyze()?;

    // We should only see one slot at some high number as according to EIP1967
    assert_eq!(layout.slot_count(), 1);

    // `bytes32`
    assert!(layout.has_slot(
        U256::from_str(
            "62783771203016910381329981606504793794820635131422253413922468358330669713901"
        )?,
        0,
        AbiType::Bytes { length: Some(32) }
    ));

    Ok(())
}
