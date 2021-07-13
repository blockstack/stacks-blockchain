use vm::costs::cost_functions::ClarityCostFunction;
use vm::costs::{cost_functions, runtime_cost, CostTracker};
use vm::errors::{
    check_argument_count, CheckErrors, Error, InterpreterError, InterpreterResult as Result,
    RuntimeErrorType,
};
use vm::representations::SymbolicExpression;
use vm::types::{
    BuffData, BufferLength, PrincipalData, QualifiedContractIdentifier, SequenceData,
    SequenceSubtype, StandardPrincipalData, TypeSignature, Value,
};
use vm::{eval, Environment, LocalContext};

use vm::database::ClarityDatabase;
use vm::database::STXBalance;

use vm::types::PrincipalProperty;

use chainstate::stacks::{
    C32_ADDRESS_VERSION_MAINNET_MULTISIG, C32_ADDRESS_VERSION_MAINNET_SINGLESIG,
    C32_ADDRESS_VERSION_TESTNET_MULTISIG, C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
};

pub fn special_is_standard(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(1, args)?;
    runtime_cost(ClarityCostFunction::Unimplemented, env, 0)?;
    let owner = eval(&args[0], env, context)?;

    let version = match owner {
        Value::Principal(PrincipalData::Standard(StandardPrincipalData(version, _bytes))) => {
            version
        }
        Value::Principal(PrincipalData::Contract(QualifiedContractIdentifier {
            issuer,
            name: _,
        })) => issuer.0,
        _ => return Err(CheckErrors::TypeValueError(TypeSignature::PrincipalType, owner).into()),
    };

    let address_is_mainnet = version == C32_ADDRESS_VERSION_MAINNET_MULTISIG
        || version == C32_ADDRESS_VERSION_MAINNET_SINGLESIG;
    let address_is_testnet = version == C32_ADDRESS_VERSION_TESTNET_MULTISIG
        || version == C32_ADDRESS_VERSION_TESTNET_SINGLESIG;
    let context_is_mainnet = env.global_context.mainnet;

    Ok(Value::Bool(
        (address_is_mainnet && context_is_mainnet) || (address_is_testnet && !context_is_mainnet),
    ))
}

pub fn special_parse_principal(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(2, args)?;
    runtime_cost(ClarityCostFunction::Unimplemented, env, 0)?;

    // Handle the block property name input arg.
    let property_name = args[0]
        .match_atom()
        .ok_or(CheckErrors::ParsePrincipalExpectPropertyName)?;

    let principal_property = PrincipalProperty::lookup_by_name(property_name).ok_or(
        CheckErrors::NoSuchParsePrincipalProperty(property_name.to_string()),
    )?;

    let principal = eval(&args[1], env, context)?;

    let (version, pub_key_hash) = match principal {
        Value::Principal(PrincipalData::Standard(StandardPrincipalData(version, bytes))) => {
            (version, bytes)
        }
        Value::Principal(PrincipalData::Contract(QualifiedContractIdentifier { issuer, name })) => {
            (issuer.0, issuer.1)
        }
        _ => {
            return Err(CheckErrors::TypeValueError(TypeSignature::PrincipalType, principal).into())
        }
    };

    let result = match principal_property {
        PrincipalProperty::Version => Value::UInt(version as u128),
        PrincipalProperty::PubKeyHash => Value::Sequence(SequenceData::Buffer(BuffData {
            data: pub_key_hash.into(),
        })),
    };
    Ok(result)
}

pub fn native_assemble_principal(version: Value, pub_key_hash: Value) -> Result<Value> {
    let verified_version = match version {
        Value::UInt(version) => version,
        _ => return Err(CheckErrors::TypeValueError(TypeSignature::UIntType, version).into()),
    };

    let verified_pub_key_hash = match pub_key_hash {
        Value::Sequence(SequenceData::Buffer(BuffData { ref data })) => data,
        _ => {
            return Err(CheckErrors::TypeValueError(
                TypeSignature::SequenceType(SequenceSubtype::BufferType(BufferLength(20))),
                pub_key_hash,
            )
            .into())
        }
    };

    if verified_pub_key_hash.len() != 20 {
        return Err(CheckErrors::TypeValueError(
            TypeSignature::SequenceType(SequenceSubtype::BufferType(BufferLength(20))),
            pub_key_hash,
        )
        .into());
    }

    let mut transfer_buffer = [0u8; 20];
    for i in 0..verified_pub_key_hash.len() {
        transfer_buffer[i] = verified_pub_key_hash[i];
    }
    let principal_data = StandardPrincipalData(verified_version as u8, transfer_buffer);
    Ok(Value::Principal(PrincipalData::Standard(principal_data)))
}
