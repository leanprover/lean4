// Lean compiler output
// Module: Lean.Compiler.IR.Checker
// Imports: public import Lean.Compiler.IR.CompilerM import Lean.Runtime
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_maxCtorScalarsSize;
extern lean_object* l_Lean_usizeSize;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_maxCtorNumObjs;
extern lean_object* l_Lean_maxCtorTag;
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqIRType_beq(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_throwCheckerError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "failed to compile definition, compiler IR check failed at `"};
static const lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__0 = (const lean_object*)&l_Lean_IR_Checker_throwCheckerError___redArg___closed__0_value;
static lean_once_cell_t l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__1;
static const lean_string_object l_Lean_IR_Checker_throwCheckerError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "`. Error: "};
static const lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__2 = (const lean_object*)&l_Lean_IR_Checker_throwCheckerError___redArg___closed__2_value;
static lean_once_cell_t l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_markVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "variable index "};
static const lean_object* l_Lean_IR_Checker_markVar___closed__0 = (const lean_object*)&l_Lean_IR_Checker_markVar___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_markVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " has already been used"};
static const lean_object* l_Lean_IR_Checker_markVar___closed__1 = (const lean_object*)&l_Lean_IR_Checker_markVar___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_markJP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "join point index "};
static const lean_object* l_Lean_IR_Checker_markJP___closed__0 = (const lean_object*)&l_Lean_IR_Checker_markJP___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_getDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "depends on declaration '"};
static const lean_object* l_Lean_IR_Checker_getDecl___closed__0 = (const lean_object*)&l_Lean_IR_Checker_getDecl___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_getDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "', which has no executable code; consider marking definition as 'noncomputable'"};
static const lean_object* l_Lean_IR_Checker_getDecl___closed__1 = (const lean_object*)&l_Lean_IR_Checker_getDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown variable '"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "x_"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkJP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown join point '"};
static const lean_object* l_Lean_IR_Checker_checkJP___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkJP___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkJP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "block_"};
static const lean_object* l_Lean_IR_Checker_checkJP___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkJP___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkEqTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 34, .m_data = "unexpected type '{ty₁}' != '{ty₂}'"};
static const lean_object* l_Lean_IR_Checker_checkEqTypes___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkEqTypes___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unexpected type '"};
static const lean_object* l_Lean_IR_Checker_checkType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkType___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_IR_Checker_checkType___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkObjType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "object expected"};
static const lean_object* l_Lean_IR_Checker_checkObjType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkObjType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkScalarType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "scalar expected"};
static const lean_object* l_Lean_IR_Checker_checkScalarType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkScalarType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkFullApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "incorrect number of arguments to '"};
static const lean_object* l_Lean_IR_Checker_checkFullApp___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkFullApp___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkFullApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "', "};
static const lean_object* l_Lean_IR_Checker_checkFullApp___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkFullApp___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkFullApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " provided, "};
static const lean_object* l_Lean_IR_Checker_checkFullApp___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkFullApp___closed__2_value;
static const lean_string_object l_Lean_IR_Checker_checkFullApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " expected"};
static const lean_object* l_Lean_IR_Checker_checkFullApp___closed__3 = (const lean_object*)&l_Lean_IR_Checker_checkFullApp___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkPartialApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "too many arguments to partial application '"};
static const lean_object* l_Lean_IR_Checker_checkPartialApp___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkPartialApp___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkPartialApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "', num. args: "};
static const lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkPartialApp___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkPartialApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", arity: "};
static const lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkPartialApp___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "constructor '"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' has too many scalar fields"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' has too many object fields"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__2_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tag for constructor '"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__3 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__3_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "' is too big, this is a limitation of the current runtime"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__4 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__4_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid proj index"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__5 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__5_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unexpected IR type '"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__6 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_withParams___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_withParams___closed__0;
static lean_once_cell_t l_Lean_IR_Checker_withParams___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_withParams___closed__1;
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__2 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__2_value;
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__3 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__3_value;
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_Checker_withParams___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__4 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_IR_checkDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_IR_checkDecl___closed__0 = (const lean_object*)&l_Lean_IR_checkDecl___closed__0_value;
static const lean_ctor_object l_Lean_IR_checkDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_IR_checkDecl___closed__1 = (const lean_object*)&l_Lean_IR_checkDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_5_);
lean_ctor_set(v___x_7_, 5, v___x_5_);
lean_ctor_set(v___x_7_, 6, v___x_5_);
lean_ctor_set(v___x_7_, 7, v___x_5_);
lean_ctor_set(v___x_7_, 8, v___x_5_);
lean_ctor_set(v___x_7_, 9, v___x_5_);
lean_ctor_set(v___x_7_, 10, v___x_5_);
lean_ctor_set(v___x_7_, 11, v___x_4_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(32u);
v___x_9_ = lean_mk_empty_array_with_capacity(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_11_ = ((size_t)5ULL);
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_unsigned_to_nat(32u);
v___x_14_ = lean_mk_empty_array_with_capacity(v___x_13_);
v___x_15_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3);
v___x_16_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_12_);
lean_ctor_set(v___x_16_, 3, v___x_12_);
lean_ctor_set_usize(v___x_16_, 4, v___x_11_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = lean_box(1);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4);
v___x_19_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
v___x_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_17_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object* v_msgData_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_toCold_26_; lean_object* v_env_27_; lean_object* v_options_28_; uint8_t v___x_29_; lean_object* v_env_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_25_ = lean_st_ref_get(v___y_23_);
v_toCold_26_ = lean_ctor_get(v___y_22_, 0);
v_env_27_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_env_27_);
lean_dec(v___x_25_);
v_options_28_ = lean_ctor_get(v_toCold_26_, 2);
v___x_29_ = 0;
v_env_30_ = l_Lean_Environment_setRecordingDeps(v_env_27_, v___x_29_);
v___x_31_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2);
v___x_32_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_28_);
v___x_33_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_33_, 0, v_env_30_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
lean_ctor_set(v___x_33_, 3, v_options_28_);
v___x_34_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v_msgData_21_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object* v_msgData_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msgData_36_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_ref_45_; lean_object* v___x_46_; lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_55_; 
v_ref_45_ = lean_ctor_get(v___y_42_, 2);
v___x_46_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msg_41_, v___y_42_, v___y_43_);
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_55_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_53_; 
lean_inc(v_ref_45_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v_ref_45_);
lean_ctor_set(v___x_51_, 1, v_a_47_);
if (v_isShared_50_ == 0)
{
lean_ctor_set_tag(v___x_49_, 1);
lean_ctor_set(v___x_49_, 0, v___x_51_);
v___x_53_ = v___x_49_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object* v_msg_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_60_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0));
v___x_63_ = l_Lean_stringToMessageData(v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__2));
v___x_66_ = l_Lean_stringToMessageData(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object* v_msg_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_currentDecl_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_currentDecl_73_ = lean_ctor_get(v_a_68_, 1);
v___x_74_ = l_Lean_IR_Decl_name(v_currentDecl_73_);
v___x_75_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__1, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1);
v___x_76_ = 0;
v___x_77_ = l_Lean_MessageData_ofConstName(v___x_74_, v___x_76_);
v___x_78_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_75_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__3, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3);
v___x_80_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = l_Lean_stringToMessageData(v_msg_67_);
v___x_82_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v___x_82_, v_a_70_, v_a_71_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object* v_msg_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object* v_00_u03b1_91_, lean_object* v_msg_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object* v_00_u03b1_99_, lean_object* v_msg_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_IR_Checker_throwCheckerError(v_00_u03b1_99_, v_msg_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object* v_00_u03b1_107_, lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_108_, v___y_111_, v___y_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object* v_00_u03b1_115_, lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(v_00_u03b1_115_, v_msg_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_122_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(lean_object* v_k_123_, lean_object* v_t_124_){
_start:
{
if (lean_obj_tag(v_t_124_) == 0)
{
lean_object* v_k_125_; lean_object* v_l_126_; lean_object* v_r_127_; uint8_t v___x_128_; 
v_k_125_ = lean_ctor_get(v_t_124_, 1);
v_l_126_ = lean_ctor_get(v_t_124_, 3);
v_r_127_ = lean_ctor_get(v_t_124_, 4);
v___x_128_ = lean_nat_dec_lt(v_k_123_, v_k_125_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_eq(v_k_123_, v_k_125_);
if (v___x_129_ == 0)
{
v_t_124_ = v_r_127_;
goto _start;
}
else
{
return v___x_129_;
}
}
else
{
v_t_124_ = v_l_126_;
goto _start;
}
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg___boxed(lean_object* v_k_133_, lean_object* v_t_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_k_133_, v_t_134_);
lean_dec(v_t_134_);
lean_dec(v_k_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(lean_object* v_k_137_, lean_object* v_v_138_, lean_object* v_t_139_){
_start:
{
if (lean_obj_tag(v_t_139_) == 0)
{
lean_object* v_size_140_; lean_object* v_k_141_; lean_object* v_v_142_; lean_object* v_l_143_; lean_object* v_r_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_425_; 
v_size_140_ = lean_ctor_get(v_t_139_, 0);
v_k_141_ = lean_ctor_get(v_t_139_, 1);
v_v_142_ = lean_ctor_get(v_t_139_, 2);
v_l_143_ = lean_ctor_get(v_t_139_, 3);
v_r_144_ = lean_ctor_get(v_t_139_, 4);
v_isSharedCheck_425_ = !lean_is_exclusive(v_t_139_);
if (v_isSharedCheck_425_ == 0)
{
v___x_146_ = v_t_139_;
v_isShared_147_ = v_isSharedCheck_425_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_r_144_);
lean_inc(v_l_143_);
lean_inc(v_v_142_);
lean_inc(v_k_141_);
lean_inc(v_size_140_);
lean_dec(v_t_139_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_425_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_lt(v_k_137_, v_k_141_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_eq(v_k_137_, v_k_141_);
if (v___x_149_ == 0)
{
lean_object* v_impl_150_; lean_object* v___x_151_; 
lean_dec(v_size_140_);
v_impl_150_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_k_137_, v_v_138_, v_r_144_);
v___x_151_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_143_) == 0)
{
lean_object* v_size_152_; lean_object* v_size_153_; lean_object* v_k_154_; lean_object* v_v_155_; lean_object* v_l_156_; lean_object* v_r_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_size_152_ = lean_ctor_get(v_l_143_, 0);
v_size_153_ = lean_ctor_get(v_impl_150_, 0);
v_k_154_ = lean_ctor_get(v_impl_150_, 1);
v_v_155_ = lean_ctor_get(v_impl_150_, 2);
v_l_156_ = lean_ctor_get(v_impl_150_, 3);
lean_inc(v_l_156_);
v_r_157_ = lean_ctor_get(v_impl_150_, 4);
v___x_158_ = lean_unsigned_to_nat(3u);
v___x_159_ = lean_nat_mul(v___x_158_, v_size_152_);
v___x_160_ = lean_nat_dec_lt(v___x_159_, v_size_153_);
lean_dec(v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
lean_dec(v_l_156_);
v___x_161_ = lean_nat_add(v___x_151_, v_size_152_);
v___x_162_ = lean_nat_add(v___x_161_, v_size_153_);
lean_dec(v___x_161_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v_impl_150_);
lean_ctor_set(v___x_146_, 0, v___x_162_);
v___x_164_ = v___x_146_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_l_143_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v_impl_150_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_229_; 
lean_inc(v_r_157_);
lean_inc(v_v_155_);
lean_inc(v_k_154_);
lean_inc(v_size_153_);
v_isSharedCheck_229_ = !lean_is_exclusive(v_impl_150_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_230_ = lean_ctor_get(v_impl_150_, 4);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_impl_150_, 3);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_impl_150_, 2);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_impl_150_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_impl_150_, 0);
lean_dec(v_unused_234_);
v___x_167_ = v_impl_150_;
v_isShared_168_ = v_isSharedCheck_229_;
goto v_resetjp_166_;
}
else
{
lean_dec(v_impl_150_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_229_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_size_169_; lean_object* v_k_170_; lean_object* v_v_171_; lean_object* v_l_172_; lean_object* v_r_173_; lean_object* v_size_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_size_169_ = lean_ctor_get(v_l_156_, 0);
v_k_170_ = lean_ctor_get(v_l_156_, 1);
v_v_171_ = lean_ctor_get(v_l_156_, 2);
v_l_172_ = lean_ctor_get(v_l_156_, 3);
v_r_173_ = lean_ctor_get(v_l_156_, 4);
v_size_174_ = lean_ctor_get(v_r_157_, 0);
v___x_175_ = lean_unsigned_to_nat(2u);
v___x_176_ = lean_nat_mul(v___x_175_, v_size_174_);
v___x_177_ = lean_nat_dec_lt(v_size_169_, v___x_176_);
lean_dec(v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_205_; 
lean_inc(v_r_173_);
lean_inc(v_l_172_);
lean_inc(v_v_171_);
lean_inc(v_k_170_);
v_isSharedCheck_205_ = !lean_is_exclusive(v_l_156_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; 
v_unused_206_ = lean_ctor_get(v_l_156_, 4);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_l_156_, 3);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_l_156_, 2);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_l_156_, 1);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_l_156_, 0);
lean_dec(v_unused_210_);
v___x_179_ = v_l_156_;
v_isShared_180_ = v_isSharedCheck_205_;
goto v_resetjp_178_;
}
else
{
lean_dec(v_l_156_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_205_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_195_; 
v___x_181_ = lean_nat_add(v___x_151_, v_size_152_);
v___x_182_ = lean_nat_add(v___x_181_, v_size_153_);
lean_dec(v_size_153_);
if (lean_obj_tag(v_l_172_) == 0)
{
lean_object* v_size_203_; 
v_size_203_ = lean_ctor_get(v_l_172_, 0);
lean_inc(v_size_203_);
v___y_195_ = v_size_203_;
goto v___jp_194_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___y_195_ = v___x_204_;
goto v___jp_194_;
}
v___jp_183_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_nat_add(v___y_184_, v___y_186_);
lean_dec(v___y_186_);
lean_dec(v___y_184_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 4, v_r_157_);
lean_ctor_set(v___x_179_, 3, v_r_173_);
lean_ctor_set(v___x_179_, 2, v_v_155_);
lean_ctor_set(v___x_179_, 1, v_k_154_);
lean_ctor_set(v___x_179_, 0, v___x_187_);
v___x_189_ = v___x_179_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_k_154_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_v_155_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_r_173_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v_r_157_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 4, v___x_189_);
lean_ctor_set(v___x_167_, 3, v___y_185_);
lean_ctor_set(v___x_167_, 2, v_v_171_);
lean_ctor_set(v___x_167_, 1, v_k_170_);
lean_ctor_set(v___x_167_, 0, v___x_182_);
v___x_191_ = v___x_167_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_k_170_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_v_171_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v___y_185_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = lean_nat_add(v___x_181_, v___y_195_);
lean_dec(v___y_195_);
lean_dec(v___x_181_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v_l_172_);
lean_ctor_set(v___x_146_, 0, v___x_196_);
v___x_198_ = v___x_146_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_l_143_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_l_172_);
v___x_198_ = v_reuseFailAlloc_202_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; 
v___x_199_ = lean_nat_add(v___x_151_, v_size_174_);
if (lean_obj_tag(v_r_173_) == 0)
{
lean_object* v_size_200_; 
v_size_200_ = lean_ctor_get(v_r_173_, 0);
lean_inc(v_size_200_);
v___y_184_ = v___x_199_;
v___y_185_ = v___x_198_;
v___y_186_ = v_size_200_;
goto v___jp_183_;
}
else
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___y_184_ = v___x_199_;
v___y_185_ = v___x_198_;
v___y_186_ = v___x_201_;
goto v___jp_183_;
}
}
}
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
lean_del_object(v___x_146_);
v___x_211_ = lean_nat_add(v___x_151_, v_size_152_);
v___x_212_ = lean_nat_add(v___x_211_, v_size_153_);
lean_dec(v_size_153_);
v___x_213_ = lean_nat_add(v___x_211_, v_size_169_);
lean_dec(v___x_211_);
lean_inc_ref(v_l_143_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 4, v_l_156_);
lean_ctor_set(v___x_167_, 3, v_l_143_);
lean_ctor_set(v___x_167_, 2, v_v_142_);
lean_ctor_set(v___x_167_, 1, v_k_141_);
lean_ctor_set(v___x_167_, 0, v___x_213_);
v___x_215_ = v___x_167_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_l_143_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_l_156_);
v___x_215_ = v_reuseFailAlloc_228_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_isSharedCheck_222_ = !lean_is_exclusive(v_l_143_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; lean_object* v_unused_224_; lean_object* v_unused_225_; lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_223_ = lean_ctor_get(v_l_143_, 4);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_l_143_, 3);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_l_143_, 2);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_l_143_, 1);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_l_143_, 0);
lean_dec(v_unused_227_);
v___x_217_ = v_l_143_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_dec(v_l_143_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 4, v_r_157_);
lean_ctor_set(v___x_217_, 3, v___x_215_);
lean_ctor_set(v___x_217_, 2, v_v_155_);
lean_ctor_set(v___x_217_, 1, v_k_154_);
lean_ctor_set(v___x_217_, 0, v___x_212_);
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_k_154_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v_v_155_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v_r_157_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_235_; 
v_l_235_ = lean_ctor_get(v_impl_150_, 3);
lean_inc(v_l_235_);
if (lean_obj_tag(v_l_235_) == 0)
{
lean_object* v_r_236_; lean_object* v_k_237_; lean_object* v_v_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_261_; 
v_r_236_ = lean_ctor_get(v_impl_150_, 4);
v_k_237_ = lean_ctor_get(v_impl_150_, 1);
v_v_238_ = lean_ctor_get(v_impl_150_, 2);
v_isSharedCheck_261_ = !lean_is_exclusive(v_impl_150_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_262_ = lean_ctor_get(v_impl_150_, 3);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_impl_150_, 0);
lean_dec(v_unused_263_);
v___x_240_ = v_impl_150_;
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_r_236_);
lean_inc(v_v_238_);
lean_inc(v_k_237_);
lean_dec(v_impl_150_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_k_242_; lean_object* v_v_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_257_; 
v_k_242_ = lean_ctor_get(v_l_235_, 1);
v_v_243_ = lean_ctor_get(v_l_235_, 2);
v_isSharedCheck_257_ = !lean_is_exclusive(v_l_235_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; 
v_unused_258_ = lean_ctor_get(v_l_235_, 4);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_l_235_, 3);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_l_235_, 0);
lean_dec(v_unused_260_);
v___x_245_ = v_l_235_;
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_v_243_);
lean_inc(v_k_242_);
lean_dec(v_l_235_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_236_, 2);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 4, v_r_236_);
lean_ctor_set(v___x_245_, 3, v_r_236_);
lean_ctor_set(v___x_245_, 2, v_v_142_);
lean_ctor_set(v___x_245_, 1, v_k_141_);
lean_ctor_set(v___x_245_, 0, v___x_151_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_r_236_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_r_236_);
v___x_249_ = v_reuseFailAlloc_256_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_251_; 
lean_inc(v_r_236_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 3, v_r_236_);
lean_ctor_set(v___x_240_, 0, v___x_151_);
v___x_251_ = v___x_240_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_r_236_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_r_236_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v___x_251_);
lean_ctor_set(v___x_146_, 3, v___x_249_);
lean_ctor_set(v___x_146_, 2, v_v_243_);
lean_ctor_set(v___x_146_, 1, v_k_242_);
lean_ctor_set(v___x_146_, 0, v___x_247_);
v___x_253_ = v___x_146_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_242_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_243_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
else
{
lean_object* v_r_264_; 
v_r_264_ = lean_ctor_get(v_impl_150_, 4);
lean_inc(v_r_264_);
if (lean_obj_tag(v_r_264_) == 0)
{
lean_object* v_k_265_; lean_object* v_v_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_277_; 
v_k_265_ = lean_ctor_get(v_impl_150_, 1);
v_v_266_ = lean_ctor_get(v_impl_150_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v_impl_150_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; 
v_unused_278_ = lean_ctor_get(v_impl_150_, 4);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_impl_150_, 3);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_impl_150_, 0);
lean_dec(v_unused_280_);
v___x_268_ = v_impl_150_;
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_v_266_);
lean_inc(v_k_265_);
lean_dec(v_impl_150_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_unsigned_to_nat(3u);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v_l_235_);
lean_ctor_set(v___x_268_, 2, v_v_142_);
lean_ctor_set(v___x_268_, 1, v_k_141_);
lean_ctor_set(v___x_268_, 0, v___x_151_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v_l_235_);
lean_ctor_set(v_reuseFailAlloc_276_, 4, v_l_235_);
v___x_272_ = v_reuseFailAlloc_276_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v_r_264_);
lean_ctor_set(v___x_146_, 3, v___x_272_);
lean_ctor_set(v___x_146_, 2, v_v_266_);
lean_ctor_set(v___x_146_, 1, v_k_265_);
lean_ctor_set(v___x_146_, 0, v___x_270_);
v___x_274_ = v___x_146_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_r_264_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(2u);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v_impl_150_);
lean_ctor_set(v___x_146_, 3, v_r_264_);
lean_ctor_set(v___x_146_, 0, v___x_281_);
v___x_283_ = v___x_146_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_r_264_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_impl_150_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
else
{
lean_object* v___x_286_; 
lean_dec(v_v_142_);
lean_dec(v_k_141_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 2, v_v_138_);
lean_ctor_set(v___x_146_, 1, v_k_137_);
v___x_286_ = v___x_146_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_size_140_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_137_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_138_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_l_143_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_r_144_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_impl_288_; lean_object* v___x_289_; 
lean_dec(v_size_140_);
v_impl_288_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_k_137_, v_v_138_, v_l_143_);
v___x_289_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_144_) == 0)
{
lean_object* v_size_290_; lean_object* v_size_291_; lean_object* v_k_292_; lean_object* v_v_293_; lean_object* v_l_294_; lean_object* v_r_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_size_290_ = lean_ctor_get(v_r_144_, 0);
v_size_291_ = lean_ctor_get(v_impl_288_, 0);
v_k_292_ = lean_ctor_get(v_impl_288_, 1);
v_v_293_ = lean_ctor_get(v_impl_288_, 2);
v_l_294_ = lean_ctor_get(v_impl_288_, 3);
v_r_295_ = lean_ctor_get(v_impl_288_, 4);
lean_inc(v_r_295_);
v___x_296_ = lean_unsigned_to_nat(3u);
v___x_297_ = lean_nat_mul(v___x_296_, v_size_290_);
v___x_298_ = lean_nat_dec_lt(v___x_297_, v_size_291_);
lean_dec(v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
lean_dec(v_r_295_);
v___x_299_ = lean_nat_add(v___x_289_, v_size_291_);
v___x_300_ = lean_nat_add(v___x_299_, v_size_290_);
lean_dec(v___x_299_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 3, v_impl_288_);
lean_ctor_set(v___x_146_, 0, v___x_300_);
v___x_302_ = v___x_146_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_impl_288_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_r_144_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
else
{
lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_369_; 
lean_inc(v_l_294_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
lean_inc(v_size_291_);
v_isSharedCheck_369_ = !lean_is_exclusive(v_impl_288_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_370_ = lean_ctor_get(v_impl_288_, 4);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_impl_288_, 3);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_impl_288_, 2);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_impl_288_, 1);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_impl_288_, 0);
lean_dec(v_unused_374_);
v___x_305_ = v_impl_288_;
v_isShared_306_ = v_isSharedCheck_369_;
goto v_resetjp_304_;
}
else
{
lean_dec(v_impl_288_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_369_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_size_307_; lean_object* v_size_308_; lean_object* v_k_309_; lean_object* v_v_310_; lean_object* v_l_311_; lean_object* v_r_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_size_307_ = lean_ctor_get(v_l_294_, 0);
v_size_308_ = lean_ctor_get(v_r_295_, 0);
v_k_309_ = lean_ctor_get(v_r_295_, 1);
v_v_310_ = lean_ctor_get(v_r_295_, 2);
v_l_311_ = lean_ctor_get(v_r_295_, 3);
v_r_312_ = lean_ctor_get(v_r_295_, 4);
v___x_313_ = lean_unsigned_to_nat(2u);
v___x_314_ = lean_nat_mul(v___x_313_, v_size_307_);
v___x_315_ = lean_nat_dec_lt(v_size_308_, v___x_314_);
lean_dec(v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_344_; 
lean_inc(v_r_312_);
lean_inc(v_l_311_);
lean_inc(v_v_310_);
lean_inc(v_k_309_);
v_isSharedCheck_344_ = !lean_is_exclusive(v_r_295_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; 
v_unused_345_ = lean_ctor_get(v_r_295_, 4);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_r_295_, 3);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_r_295_, 2);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_r_295_, 1);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_r_295_, 0);
lean_dec(v_unused_349_);
v___x_317_ = v_r_295_;
v_isShared_318_ = v_isSharedCheck_344_;
goto v_resetjp_316_;
}
else
{
lean_dec(v_r_295_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_344_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___x_332_; lean_object* v___y_334_; 
v___x_319_ = lean_nat_add(v___x_289_, v_size_291_);
lean_dec(v_size_291_);
v___x_320_ = lean_nat_add(v___x_319_, v_size_290_);
lean_dec(v___x_319_);
v___x_332_ = lean_nat_add(v___x_289_, v_size_307_);
if (lean_obj_tag(v_l_311_) == 0)
{
lean_object* v_size_342_; 
v_size_342_ = lean_ctor_get(v_l_311_, 0);
lean_inc(v_size_342_);
v___y_334_ = v_size_342_;
goto v___jp_333_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___y_334_ = v___x_343_;
goto v___jp_333_;
}
v___jp_321_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_nat_add(v___y_322_, v___y_324_);
lean_dec(v___y_324_);
lean_dec(v___y_322_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 4, v_r_144_);
lean_ctor_set(v___x_317_, 3, v_r_312_);
lean_ctor_set(v___x_317_, 2, v_v_142_);
lean_ctor_set(v___x_317_, 1, v_k_141_);
lean_ctor_set(v___x_317_, 0, v___x_325_);
v___x_327_ = v___x_317_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_r_312_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_r_144_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_329_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 4, v___x_327_);
lean_ctor_set(v___x_305_, 3, v___y_323_);
lean_ctor_set(v___x_305_, 2, v_v_310_);
lean_ctor_set(v___x_305_, 1, v_k_309_);
lean_ctor_set(v___x_305_, 0, v___x_320_);
v___x_329_ = v___x_305_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_k_309_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_v_310_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v___y_323_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_nat_add(v___x_332_, v___y_334_);
lean_dec(v___y_334_);
lean_dec(v___x_332_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v_l_311_);
lean_ctor_set(v___x_146_, 3, v_l_294_);
lean_ctor_set(v___x_146_, 2, v_v_293_);
lean_ctor_set(v___x_146_, 1, v_k_292_);
lean_ctor_set(v___x_146_, 0, v___x_335_);
v___x_337_ = v___x_146_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_292_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_293_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_l_294_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_l_311_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; 
v___x_338_ = lean_nat_add(v___x_289_, v_size_290_);
if (lean_obj_tag(v_r_312_) == 0)
{
lean_object* v_size_339_; 
v_size_339_ = lean_ctor_get(v_r_312_, 0);
lean_inc(v_size_339_);
v___y_322_ = v___x_338_;
v___y_323_ = v___x_337_;
v___y_324_ = v_size_339_;
goto v___jp_321_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_unsigned_to_nat(0u);
v___y_322_ = v___x_338_;
v___y_323_ = v___x_337_;
v___y_324_ = v___x_340_;
goto v___jp_321_;
}
}
}
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
lean_del_object(v___x_146_);
v___x_350_ = lean_nat_add(v___x_289_, v_size_291_);
lean_dec(v_size_291_);
v___x_351_ = lean_nat_add(v___x_350_, v_size_290_);
lean_dec(v___x_350_);
v___x_352_ = lean_nat_add(v___x_289_, v_size_290_);
v___x_353_ = lean_nat_add(v___x_352_, v_size_308_);
lean_dec(v___x_352_);
lean_inc_ref(v_r_144_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 4, v_r_144_);
lean_ctor_set(v___x_305_, 3, v_r_295_);
lean_ctor_set(v___x_305_, 2, v_v_142_);
lean_ctor_set(v___x_305_, 1, v_k_141_);
lean_ctor_set(v___x_305_, 0, v___x_353_);
v___x_355_ = v___x_305_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_r_295_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_r_144_);
v___x_355_ = v_reuseFailAlloc_368_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
v_isSharedCheck_362_ = !lean_is_exclusive(v_r_144_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; lean_object* v_unused_364_; lean_object* v_unused_365_; lean_object* v_unused_366_; lean_object* v_unused_367_; 
v_unused_363_ = lean_ctor_get(v_r_144_, 4);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_r_144_, 3);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_r_144_, 2);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_r_144_, 1);
lean_dec(v_unused_366_);
v_unused_367_ = lean_ctor_get(v_r_144_, 0);
lean_dec(v_unused_367_);
v___x_357_ = v_r_144_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_dec(v_r_144_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 4, v___x_355_);
lean_ctor_set(v___x_357_, 3, v_l_294_);
lean_ctor_set(v___x_357_, 2, v_v_293_);
lean_ctor_set(v___x_357_, 1, v_k_292_);
lean_ctor_set(v___x_357_, 0, v___x_351_);
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_k_292_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_v_293_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_l_294_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v___x_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_375_; 
v_l_375_ = lean_ctor_get(v_impl_288_, 3);
if (lean_obj_tag(v_l_375_) == 0)
{
lean_object* v_r_376_; lean_object* v_k_377_; lean_object* v_v_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_389_; 
lean_inc_ref(v_l_375_);
v_r_376_ = lean_ctor_get(v_impl_288_, 4);
v_k_377_ = lean_ctor_get(v_impl_288_, 1);
v_v_378_ = lean_ctor_get(v_impl_288_, 2);
v_isSharedCheck_389_ = !lean_is_exclusive(v_impl_288_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; lean_object* v_unused_391_; 
v_unused_390_ = lean_ctor_get(v_impl_288_, 3);
lean_dec(v_unused_390_);
v_unused_391_ = lean_ctor_get(v_impl_288_, 0);
lean_dec(v_unused_391_);
v___x_380_ = v_impl_288_;
v_isShared_381_ = v_isSharedCheck_389_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_r_376_);
lean_inc(v_v_378_);
lean_inc(v_k_377_);
lean_dec(v_impl_288_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_389_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_376_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 3, v_r_376_);
lean_ctor_set(v___x_380_, 2, v_v_142_);
lean_ctor_set(v___x_380_, 1, v_k_141_);
lean_ctor_set(v___x_380_, 0, v___x_289_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_r_376_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_r_376_);
v___x_384_ = v_reuseFailAlloc_388_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v___x_384_);
lean_ctor_set(v___x_146_, 3, v_l_375_);
lean_ctor_set(v___x_146_, 2, v_v_378_);
lean_ctor_set(v___x_146_, 1, v_k_377_);
lean_ctor_set(v___x_146_, 0, v___x_382_);
v___x_386_ = v___x_146_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_k_377_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_v_378_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v_l_375_);
lean_ctor_set(v_reuseFailAlloc_387_, 4, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_r_392_; 
v_r_392_ = lean_ctor_get(v_impl_288_, 4);
lean_inc(v_r_392_);
if (lean_obj_tag(v_r_392_) == 0)
{
lean_object* v_k_393_; lean_object* v_v_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_417_; 
lean_inc(v_l_375_);
v_k_393_ = lean_ctor_get(v_impl_288_, 1);
v_v_394_ = lean_ctor_get(v_impl_288_, 2);
v_isSharedCheck_417_ = !lean_is_exclusive(v_impl_288_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; lean_object* v_unused_419_; lean_object* v_unused_420_; 
v_unused_418_ = lean_ctor_get(v_impl_288_, 4);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_impl_288_, 3);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_impl_288_, 0);
lean_dec(v_unused_420_);
v___x_396_ = v_impl_288_;
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_v_394_);
lean_inc(v_k_393_);
lean_dec(v_impl_288_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_k_398_; lean_object* v_v_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_413_; 
v_k_398_ = lean_ctor_get(v_r_392_, 1);
v_v_399_ = lean_ctor_get(v_r_392_, 2);
v_isSharedCheck_413_ = !lean_is_exclusive(v_r_392_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_414_ = lean_ctor_get(v_r_392_, 4);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_r_392_, 3);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_r_392_, 0);
lean_dec(v_unused_416_);
v___x_401_ = v_r_392_;
v_isShared_402_ = v_isSharedCheck_413_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_v_399_);
lean_inc(v_k_398_);
lean_dec(v_r_392_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_413_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(3u);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 4, v_l_375_);
lean_ctor_set(v___x_401_, 3, v_l_375_);
lean_ctor_set(v___x_401_, 2, v_v_394_);
lean_ctor_set(v___x_401_, 1, v_k_393_);
lean_ctor_set(v___x_401_, 0, v___x_289_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_k_393_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_v_394_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_l_375_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_l_375_);
v___x_405_ = v_reuseFailAlloc_412_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 4, v_l_375_);
lean_ctor_set(v___x_396_, 2, v_v_142_);
lean_ctor_set(v___x_396_, 1, v_k_141_);
lean_ctor_set(v___x_396_, 0, v___x_289_);
v___x_407_ = v___x_396_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_l_375_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_l_375_);
v___x_407_ = v_reuseFailAlloc_411_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v___x_407_);
lean_ctor_set(v___x_146_, 3, v___x_405_);
lean_ctor_set(v___x_146_, 2, v_v_399_);
lean_ctor_set(v___x_146_, 1, v_k_398_);
lean_ctor_set(v___x_146_, 0, v___x_403_);
v___x_409_ = v___x_146_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_398_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_399_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_unsigned_to_nat(2u);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v_r_392_);
lean_ctor_set(v___x_146_, 3, v_impl_288_);
lean_ctor_set(v___x_146_, 0, v___x_421_);
v___x_423_ = v___x_146_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_k_141_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_v_142_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_impl_288_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_r_392_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_k_137_);
lean_ctor_set(v___x_427_, 2, v_v_138_);
lean_ctor_set(v___x_427_, 3, v_t_139_);
lean_ctor_set(v___x_427_, 4, v_t_139_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* v_x_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v_foundJPs_439_; lean_object* v___y_440_; lean_object* v___y_445_; lean_object* v___x_452_; lean_object* v_foundVars_453_; uint8_t v___x_454_; 
v___x_452_ = lean_st_ref_get(v_a_432_);
v_foundVars_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_foundVars_453_);
lean_dec(v___x_452_);
v___x_454_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_x_430_, v_foundVars_453_);
lean_dec(v_foundVars_453_);
if (v___x_454_ == 0)
{
v___y_445_ = v_a_432_;
goto v___jp_444_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_455_ = ((lean_object*)(l_Lean_IR_Checker_markVar___closed__0));
v___x_456_ = l_Nat_reprFast(v_x_430_);
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
lean_dec_ref(v___x_456_);
v___x_458_ = ((lean_object*)(l_Lean_IR_Checker_markVar___closed__1));
v___x_459_ = lean_string_append(v___x_457_, v___x_458_);
v___x_460_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_459_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
return v___x_460_;
}
v___jp_436_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___y_440_);
lean_ctor_set(v___x_441_, 1, v_foundJPs_439_);
v___x_442_ = lean_st_ref_put(v___y_437_, v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___y_438_);
return v___x_443_;
}
v___jp_444_:
{
lean_object* v___x_446_; lean_object* v_foundVars_447_; lean_object* v_foundJPs_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_446_ = lean_st_ref_take(v___y_445_);
v_foundVars_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_foundVars_447_);
v_foundJPs_448_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_foundJPs_448_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v___x_450_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_x_430_, v_foundVars_447_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_x_430_, v___x_449_, v_foundVars_447_);
v___y_437_ = v___y_445_;
v___y_438_ = v___x_449_;
v_foundJPs_439_ = v_foundJPs_448_;
v___y_440_ = v___x_451_;
goto v___jp_436_;
}
else
{
lean_dec(v_x_430_);
v___y_437_ = v___y_445_;
v___y_438_ = v___x_449_;
v_foundJPs_439_ = v_foundJPs_448_;
v___y_440_ = v_foundVars_447_;
goto v___jp_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* v_x_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_IR_Checker_markVar(v_x_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
return v_res_467_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0(lean_object* v_00_u03b2_468_, lean_object* v_k_469_, lean_object* v_t_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_k_469_, v_t_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___boxed(lean_object* v_00_u03b2_472_, lean_object* v_k_473_, lean_object* v_t_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0(v_00_u03b2_472_, v_k_473_, v_t_474_);
lean_dec(v_t_474_);
lean_dec(v_k_473_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1(lean_object* v_00_u03b2_477_, lean_object* v_k_478_, lean_object* v_v_479_, lean_object* v_t_480_, lean_object* v_hl_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_k_478_, v_v_479_, v_t_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* v_j_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_499_; lean_object* v___x_506_; lean_object* v_foundJPs_507_; uint8_t v___x_508_; 
v___x_506_ = lean_st_ref_get(v_a_486_);
v_foundJPs_507_ = lean_ctor_get(v___x_506_, 1);
lean_inc(v_foundJPs_507_);
lean_dec(v___x_506_);
v___x_508_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_j_484_, v_foundJPs_507_);
lean_dec(v_foundJPs_507_);
if (v___x_508_ == 0)
{
v___y_499_ = v_a_486_;
goto v___jp_498_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_509_ = ((lean_object*)(l_Lean_IR_Checker_markJP___closed__0));
v___x_510_ = l_Nat_reprFast(v_j_484_);
v___x_511_ = lean_string_append(v___x_509_, v___x_510_);
lean_dec_ref(v___x_510_);
v___x_512_ = ((lean_object*)(l_Lean_IR_Checker_markVar___closed__1));
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
v___x_514_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_513_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
return v___x_514_;
}
v___jp_490_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___y_493_);
lean_ctor_set(v___x_495_, 1, v___y_494_);
v___x_496_ = lean_st_ref_put(v___y_491_, v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___y_492_);
return v___x_497_;
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v_foundVars_501_; lean_object* v_foundJPs_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_500_ = lean_st_ref_take(v___y_499_);
v_foundVars_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_foundVars_501_);
v_foundJPs_502_ = lean_ctor_get(v___x_500_, 1);
lean_inc(v_foundJPs_502_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v___x_504_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_j_484_, v_foundJPs_502_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_j_484_, v___x_503_, v_foundJPs_502_);
v___y_491_ = v___y_499_;
v___y_492_ = v___x_503_;
v___y_493_ = v_foundVars_501_;
v___y_494_ = v___x_505_;
goto v___jp_490_;
}
else
{
lean_dec(v_j_484_);
v___y_491_ = v___y_499_;
v___y_492_ = v___x_503_;
v___y_493_ = v_foundVars_501_;
v___y_494_ = v_foundJPs_502_;
goto v___jp_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* v_j_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_IR_Checker_markJP(v_j_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* v_c_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_530_; lean_object* v_env_531_; lean_object* v_decls_532_; lean_object* v___x_533_; 
v___x_530_ = lean_st_ref_get(v_a_528_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_env_531_);
lean_dec(v___x_530_);
v_decls_532_ = lean_ctor_get(v_a_525_, 2);
lean_inc(v_c_524_);
v___x_533_ = l_Lean_IR_findEnvDecl_x27(v_env_531_, v_c_524_, v_decls_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_534_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
v___x_535_ = 1;
v___x_536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_524_, v___x_535_);
v___x_537_ = lean_string_append(v___x_534_, v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v___x_540_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_539_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
return v___x_540_;
}
else
{
lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_c_524_);
v_val_541_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_533_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_dec(v___x_533_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_val_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* v_c_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_IR_Checker_getDecl(v_c_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* v_x_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
uint8_t v___y_566_; lean_object* v_localCtx_577_; uint8_t v___x_578_; 
v_localCtx_577_ = lean_ctor_get(v_a_560_, 0);
v___x_578_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_577_, v_x_559_);
if (v___x_578_ == 0)
{
uint8_t v___x_579_; 
v___x_579_ = l_Lean_IR_LocalContext_isParam(v_localCtx_577_, v_x_559_);
v___y_566_ = v___x_579_;
goto v___jp_565_;
}
else
{
v___y_566_ = v___x_578_;
goto v___jp_565_;
}
v___jp_565_:
{
if (v___y_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_567_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_568_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_569_ = l_Nat_reprFast(v_x_559_);
v___x_570_ = lean_string_append(v___x_568_, v___x_569_);
lean_dec_ref(v___x_569_);
v___x_571_ = lean_string_append(v___x_567_, v___x_570_);
lean_dec_ref(v___x_570_);
v___x_572_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_573_ = lean_string_append(v___x_571_, v___x_572_);
v___x_574_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_573_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec(v_x_559_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_IR_Checker_checkVar(v_x_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_localCtx_595_; uint8_t v___x_596_; 
v_localCtx_595_ = lean_ctor_get(v_a_590_, 0);
v___x_596_ = l_Lean_IR_LocalContext_isJP(v_localCtx_595_, v_j_589_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_597_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_598_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_599_ = l_Nat_reprFast(v_j_589_);
v___x_600_ = lean_string_append(v___x_598_, v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = lean_string_append(v___x_597_, v___x_600_);
lean_dec_ref(v___x_600_);
v___x_602_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_603_ = lean_string_append(v___x_601_, v___x_602_);
v___x_604_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_603_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_j_589_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_IR_Checker_checkJP(v_j_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
if (lean_obj_tag(v_a_614_) == 0)
{
lean_object* v_id_620_; lean_object* v___x_621_; 
v_id_620_ = lean_ctor_get(v_a_614_, 0);
lean_inc(v_id_620_);
lean_dec_ref_known(v_a_614_, 1);
v___x_621_ = l_Lean_IR_Checker_checkVar(v_id_620_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
return v___x_621_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_box(0);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_IR_Checker_checkArg(v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_631_, size_t v_i_632_, size_t v_stop_633_, lean_object* v_b_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_eq(v_i_632_, v_stop_633_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_array_uget_borrowed(v_as_631_, v_i_632_);
lean_inc(v___x_641_);
v___x_642_ = l_Lean_IR_Checker_checkArg(v___x_641_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; size_t v___x_644_; size_t v___x_645_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_632_, v___x_644_);
v_i_632_ = v___x_645_;
v_b_634_ = v_a_643_;
goto _start;
}
else
{
return v___x_642_;
}
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v_b_634_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_648_, lean_object* v_i_649_, lean_object* v_stop_650_, lean_object* v_b_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
size_t v_i_boxed_657_; size_t v_stop_boxed_658_; lean_object* v_res_659_; 
v_i_boxed_657_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_stop_boxed_658_ = lean_unbox_usize(v_stop_650_);
lean_dec(v_stop_650_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_648_, v_i_boxed_657_, v_stop_boxed_658_, v_b_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v_as_648_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v_as_660_);
v___x_668_ = lean_box(0);
v___x_669_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
return v___x_670_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = lean_nat_dec_le(v___x_667_, v___x_667_);
if (v___x_671_ == 0)
{
if (v___x_669_ == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_668_);
return v___x_672_;
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_667_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_660_, v___x_673_, v___x_674_, v___x_668_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v___x_675_;
}
}
else
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_676_ = ((size_t)0ULL);
v___x_677_ = lean_usize_of_nat(v___x_667_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_660_, v___x_676_, v___x_677_, v___x_668_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_IR_Checker_checkArgs(v_as_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec_ref(v_as_679_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_687_, lean_object* v_ty_u2082_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_687_, v_ty_u2082_688_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_696_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_695_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(0);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_699_, lean_object* v_ty_u2082_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_699_, v_ty_u2082_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_ty_u2082_700_);
lean_dec(v_ty_u2081_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_709_, lean_object* v_p_710_, lean_object* v_suffix_x3f_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
lean_inc(v_ty_709_);
v___x_717_ = lean_apply_1(v_p_710_, v_ty_709_);
v___x_718_ = lean_unbox(v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_msg_726_; 
v___x_719_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_720_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_709_);
v___x_721_ = l_Std_Format_defWidth;
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = l_Std_Format_pretty(v___x_720_, v___x_721_, v___x_722_, v___x_722_);
v___x_724_ = lean_string_append(v___x_719_, v___x_723_);
lean_dec_ref(v___x_723_);
v___x_725_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_726_ = lean_string_append(v___x_724_, v___x_725_);
if (lean_obj_tag(v_suffix_x3f_711_) == 1)
{
lean_object* v_val_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_msg_730_; lean_object* v___x_731_; 
v_val_727_ = lean_ctor_get(v_suffix_x3f_711_, 0);
v___x_728_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_729_ = lean_string_append(v_msg_726_, v___x_728_);
v_msg_730_ = lean_string_append(v___x_729_, v_val_727_);
v___x_731_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_730_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_726_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
return v___x_732_;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v_ty_709_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_735_, lean_object* v_p_736_, lean_object* v_suffix_x3f_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_IR_Checker_checkType(v_ty_735_, v_p_736_, v_suffix_x3f_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_suffix_x3f_737_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = l_Lean_IR_IRType_isObj(v_ty_745_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_msg_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_msg_763_; lean_object* v___x_764_; 
v___x_752_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_753_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_754_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_745_);
v___x_755_ = l_Std_Format_defWidth;
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = l_Std_Format_pretty(v___x_754_, v___x_755_, v___x_756_, v___x_756_);
v___x_758_ = lean_string_append(v___x_753_, v___x_757_);
lean_dec_ref(v___x_757_);
v___x_759_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_760_ = lean_string_append(v___x_758_, v___x_759_);
v___x_761_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_762_ = lean_string_append(v_msg_760_, v___x_761_);
v_msg_763_ = lean_string_append(v___x_762_, v___x_752_);
v___x_764_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_763_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v_ty_745_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_IR_Checker_checkObjType(v_ty_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = l_Lean_IR_IRType_isScalar(v_ty_775_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_msg_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_msg_793_; lean_object* v___x_794_; 
v___x_782_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_783_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_784_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_775_);
v___x_785_ = l_Std_Format_defWidth;
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = l_Std_Format_pretty(v___x_784_, v___x_785_, v___x_786_, v___x_786_);
v___x_788_ = lean_string_append(v___x_783_, v___x_787_);
lean_dec_ref(v___x_787_);
v___x_789_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_790_ = lean_string_append(v___x_788_, v___x_789_);
v___x_791_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_792_ = lean_string_append(v_msg_790_, v___x_791_);
v_msg_793_ = lean_string_append(v___x_792_, v___x_782_);
v___x_794_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_793_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v_ty_775_);
v___x_795_ = lean_box(0);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_IR_Checker_checkScalarType(v_ty_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_localCtx_810_; lean_object* v___x_811_; 
v_localCtx_810_ = lean_ctor_get(v_a_805_, 0);
v___x_811_ = l_Lean_IR_LocalContext_getType(v_localCtx_810_, v_x_804_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_812_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_813_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_814_ = l_Nat_reprFast(v_x_804_);
v___x_815_ = lean_string_append(v___x_813_, v___x_814_);
lean_dec_ref(v___x_814_);
v___x_816_ = lean_string_append(v___x_812_, v___x_815_);
lean_dec_ref(v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_818_ = lean_string_append(v___x_816_, v___x_817_);
v___x_819_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_818_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
return v___x_819_;
}
else
{
lean_object* v_val_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_x_804_);
v_val_820_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_811_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_val_820_);
lean_dec(v___x_811_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_val_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_IR_Checker_getType(v_x_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_835_, lean_object* v_p_836_, lean_object* v_suffix_x3f_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_IR_Checker_getType(v_x_835_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_868_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_868_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_868_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_868_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
lean_inc(v_a_844_);
v___x_848_ = lean_apply_1(v_p_836_, v_a_844_);
v___x_849_ = lean_unbox(v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_msg_857_; 
lean_del_object(v___x_846_);
v___x_850_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_851_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_844_);
v___x_852_ = l_Std_Format_defWidth;
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = l_Std_Format_pretty(v___x_851_, v___x_852_, v___x_853_, v___x_853_);
v___x_855_ = lean_string_append(v___x_850_, v___x_854_);
lean_dec_ref(v___x_854_);
v___x_856_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_857_ = lean_string_append(v___x_855_, v___x_856_);
if (lean_obj_tag(v_suffix_x3f_837_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_msg_861_; lean_object* v___x_862_; 
v_val_858_ = lean_ctor_get(v_suffix_x3f_837_, 0);
v___x_859_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_860_ = lean_string_append(v_msg_857_, v___x_859_);
v_msg_861_ = lean_string_append(v___x_860_, v_val_858_);
v___x_862_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_861_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_857_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
return v___x_863_;
}
}
else
{
lean_object* v___x_864_; lean_object* v___x_866_; 
lean_dec(v_a_844_);
v___x_864_ = lean_box(0);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_864_);
v___x_866_ = v___x_846_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v_p_836_);
v_a_869_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_843_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_843_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_877_, lean_object* v_p_878_, lean_object* v_suffix_x3f_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_IR_Checker_checkVarType(v_x_877_, v_p_878_, v_suffix_x3f_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_suffix_x3f_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_893_ = l_Lean_IR_Checker_getType(v_x_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_915_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_915_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_915_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_915_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
uint8_t v___x_898_; 
v___x_898_ = l_Lean_IR_IRType_isObj(v_a_894_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_msg_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_msg_909_; lean_object* v___x_910_; 
lean_del_object(v___x_896_);
v___x_899_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_900_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_894_);
v___x_901_ = l_Std_Format_defWidth;
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = l_Std_Format_pretty(v___x_900_, v___x_901_, v___x_902_, v___x_902_);
v___x_904_ = lean_string_append(v___x_899_, v___x_903_);
lean_dec_ref(v___x_903_);
v___x_905_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_906_ = lean_string_append(v___x_904_, v___x_905_);
v___x_907_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_908_ = lean_string_append(v_msg_906_, v___x_907_);
v_msg_909_ = lean_string_append(v___x_908_, v___x_892_);
v___x_910_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_909_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec(v_a_894_);
v___x_911_ = lean_box(0);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_911_);
v___x_913_ = v___x_896_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_a_916_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_893_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_893_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_IR_Checker_checkObjVar(v_x_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_938_ = l_Lean_IR_Checker_getType(v_x_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_960_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_960_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_960_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_960_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
uint8_t v___x_943_; 
v___x_943_ = l_Lean_IR_IRType_isScalar(v_a_939_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_msg_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_msg_954_; lean_object* v___x_955_; 
lean_del_object(v___x_941_);
v___x_944_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_945_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_939_);
v___x_946_ = l_Std_Format_defWidth;
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = l_Std_Format_pretty(v___x_945_, v___x_946_, v___x_947_, v___x_947_);
v___x_949_ = lean_string_append(v___x_944_, v___x_948_);
lean_dec_ref(v___x_948_);
v___x_950_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_951_ = lean_string_append(v___x_949_, v___x_950_);
v___x_952_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_953_ = lean_string_append(v_msg_951_, v___x_952_);
v_msg_954_ = lean_string_append(v___x_953_, v___x_937_);
v___x_955_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_954_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_958_; 
lean_dec(v_a_939_);
v___x_956_ = lean_box(0);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_956_);
v___x_958_ = v___x_941_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_938_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_938_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_IR_Checker_checkScalarVar(v_x_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_980_, lean_object* v_ys_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; 
lean_inc(v_c_980_);
v___x_987_ = l_Lean_IR_Checker_getDecl(v_c_980_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_array_get_size(v_ys_981_);
v___x_990_ = l_Lean_IR_Decl_params(v_a_988_);
lean_dec(v_a_988_);
v___x_991_ = lean_array_get_size(v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = lean_nat_dec_eq(v___x_989_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_993_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_994_ = 1;
v___x_995_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_980_, v___x_994_);
v___x_996_ = lean_string_append(v___x_993_, v___x_995_);
lean_dec_ref(v___x_995_);
v___x_997_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_998_ = lean_string_append(v___x_996_, v___x_997_);
v___x_999_ = l_Nat_reprFast(v___x_989_);
v___x_1000_ = lean_string_append(v___x_998_, v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_1002_ = lean_string_append(v___x_1000_, v___x_1001_);
v___x_1003_ = l_Nat_reprFast(v___x_991_);
v___x_1004_ = lean_string_append(v___x_1002_, v___x_1003_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_1006_ = lean_string_append(v___x_1004_, v___x_1005_);
v___x_1007_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1006_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; 
lean_dec(v_c_980_);
v___x_1008_ = l_Lean_IR_Checker_checkArgs(v_ys_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
return v___x_1008_;
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_c_980_);
v_a_1009_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_987_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_987_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_1017_, lean_object* v_ys_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_IR_Checker_checkFullApp(v_c_1017_, v_ys_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec_ref(v_ys_1018_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1028_, lean_object* v_ys_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; 
lean_inc(v_c_1028_);
v___x_1035_ = l_Lean_IR_Checker_getDecl(v_c_1028_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = lean_array_get_size(v_ys_1029_);
v___x_1038_ = l_Lean_IR_Decl_params(v_a_1036_);
lean_dec(v_a_1036_);
v___x_1039_ = lean_array_get_size(v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = lean_nat_dec_lt(v___x_1037_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1041_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1042_ = 1;
v___x_1043_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1028_, v___x_1042_);
v___x_1044_ = lean_string_append(v___x_1041_, v___x_1043_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
v___x_1047_ = l_Nat_reprFast(v___x_1037_);
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
v___x_1051_ = l_Nat_reprFast(v___x_1039_);
v___x_1052_ = lean_string_append(v___x_1050_, v___x_1051_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1052_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; 
lean_dec(v_c_1028_);
v___x_1054_ = l_Lean_IR_Checker_checkArgs(v_ys_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
return v___x_1054_;
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_c_1028_);
v_a_1055_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1035_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1035_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1063_, lean_object* v_ys_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_IR_Checker_checkPartialApp(v_c_1063_, v_ys_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec_ref(v_ys_1064_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1078_, lean_object* v_e_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
switch(lean_obj_tag(v_e_1079_))
{
case 0:
{
lean_object* v_i_1085_; lean_object* v_ys_1086_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v_name_1097_; lean_object* v_cidx_1098_; lean_object* v_size_1099_; lean_object* v_usize_1100_; lean_object* v_ssize_1101_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_i_1085_ = lean_ctor_get(v_e_1079_, 0);
lean_inc_ref(v_i_1085_);
v_ys_1086_ = lean_ctor_get(v_e_1079_, 1);
lean_inc_ref(v_ys_1086_);
lean_dec_ref_known(v_e_1079_, 2);
v_name_1097_ = lean_ctor_get(v_i_1085_, 0);
v_cidx_1098_ = lean_ctor_get(v_i_1085_, 1);
v_size_1099_ = lean_ctor_get(v_i_1085_, 2);
v_usize_1100_ = lean_ctor_get(v_i_1085_, 3);
v_ssize_1101_ = lean_ctor_get(v_i_1085_, 4);
v___x_1131_ = l_Lean_maxCtorTag;
v___x_1132_ = lean_nat_dec_lt(v___x_1131_, v_cidx_1098_);
if (v___x_1132_ == 0)
{
v___y_1119_ = v_a_1080_;
v___y_1120_ = v_a_1081_;
v___y_1121_ = v_a_1082_;
v___y_1122_ = v_a_1083_;
goto v___jp_1118_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Lean_IR_CtorInfo_isRef(v_i_1085_);
if (v___x_1133_ == 0)
{
v___y_1119_ = v_a_1080_;
v___y_1120_ = v_a_1081_;
v___y_1121_ = v_a_1082_;
v___y_1122_ = v_a_1083_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc(v_name_1097_);
lean_dec_ref(v_ys_1086_);
lean_dec_ref(v_i_1085_);
lean_dec(v_ty_1078_);
v___x_1134_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1135_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1097_, v___x_1133_);
v___x_1136_ = lean_string_append(v___x_1134_, v___x_1135_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1138_ = lean_string_append(v___x_1136_, v___x_1137_);
v___x_1139_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1138_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1139_;
}
}
v___jp_1087_:
{
uint8_t v___x_1092_; 
v___x_1092_ = l_Lean_IR_CtorInfo_isRef(v_i_1085_);
lean_dec_ref(v_i_1085_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec_ref(v_ys_1086_);
lean_dec(v_ty_1078_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref_known(v___x_1095_, 1);
v___x_1096_ = l_Lean_IR_Checker_checkArgs(v_ys_1086_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec_ref(v_ys_1086_);
return v___x_1096_;
}
else
{
lean_dec_ref(v_ys_1086_);
return v___x_1095_;
}
}
}
v___jp_1102_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1107_ = l_Lean_maxCtorScalarsSize;
v___x_1108_ = l_Lean_usizeSize;
v___x_1109_ = lean_nat_mul(v_usize_1100_, v___x_1108_);
v___x_1110_ = lean_nat_add(v_ssize_1101_, v___x_1109_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_nat_dec_lt(v___x_1107_, v___x_1110_);
lean_dec(v___x_1110_);
if (v___x_1111_ == 0)
{
v___y_1088_ = v___y_1103_;
v___y_1089_ = v___y_1104_;
v___y_1090_ = v___y_1105_;
v___y_1091_ = v___y_1106_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_inc(v_name_1097_);
lean_dec_ref(v_ys_1086_);
lean_dec_ref(v_i_1085_);
lean_dec(v_ty_1078_);
v___x_1112_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1113_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1097_, v___x_1111_);
v___x_1114_ = lean_string_append(v___x_1112_, v___x_1113_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1116_ = lean_string_append(v___x_1114_, v___x_1115_);
v___x_1117_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1116_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
return v___x_1117_;
}
}
v___jp_1118_:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = l_Lean_maxCtorNumObjs;
v___x_1124_ = lean_nat_dec_lt(v___x_1123_, v_size_1099_);
if (v___x_1124_ == 0)
{
v___y_1103_ = v___y_1119_;
v___y_1104_ = v___y_1120_;
v___y_1105_ = v___y_1121_;
v___y_1106_ = v___y_1122_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_inc(v_name_1097_);
lean_dec_ref(v_ys_1086_);
lean_dec_ref(v_i_1085_);
lean_dec(v_ty_1078_);
v___x_1125_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1126_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1097_, v___x_1124_);
v___x_1127_ = lean_string_append(v___x_1125_, v___x_1126_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1129_ = lean_string_append(v___x_1127_, v___x_1128_);
v___x_1130_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1129_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
return v___x_1130_;
}
}
}
case 1:
{
lean_object* v_x_1140_; lean_object* v___x_1141_; 
v_x_1140_ = lean_ctor_get(v_e_1079_, 1);
lean_inc(v_x_1140_);
lean_dec_ref_known(v_e_1079_, 2);
v___x_1141_ = l_Lean_IR_Checker_checkObjVar(v_x_1140_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; 
lean_dec_ref_known(v___x_1141_, 1);
v___x_1142_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1142_;
}
else
{
lean_dec(v_ty_1078_);
return v___x_1141_;
}
}
case 2:
{
lean_object* v_x_1143_; lean_object* v_ys_1144_; lean_object* v___x_1145_; 
v_x_1143_ = lean_ctor_get(v_e_1079_, 0);
lean_inc(v_x_1143_);
v_ys_1144_ = lean_ctor_get(v_e_1079_, 2);
lean_inc_ref(v_ys_1144_);
lean_dec_ref_known(v_e_1079_, 3);
v___x_1145_ = l_Lean_IR_Checker_checkObjVar(v_x_1143_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; 
lean_dec_ref_known(v___x_1145_, 1);
v___x_1146_ = l_Lean_IR_Checker_checkArgs(v_ys_1144_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec_ref(v_ys_1144_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; 
lean_dec_ref_known(v___x_1146_, 1);
v___x_1147_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1147_;
}
else
{
lean_dec(v_ty_1078_);
return v___x_1146_;
}
}
else
{
lean_dec_ref(v_ys_1144_);
lean_dec(v_ty_1078_);
return v___x_1145_;
}
}
case 3:
{
lean_object* v_i_1148_; lean_object* v_x_1149_; lean_object* v___x_1150_; 
v_i_1148_ = lean_ctor_get(v_e_1079_, 0);
lean_inc(v_i_1148_);
v_x_1149_ = lean_ctor_get(v_e_1079_, 1);
lean_inc(v_x_1149_);
lean_dec_ref_known(v_e_1079_, 2);
v___x_1150_ = l_Lean_IR_Checker_getType(v_x_1149_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1196_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1196_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1196_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
switch(lean_obj_tag(v_a_1151_))
{
case 7:
{
lean_object* v___x_1155_; 
lean_del_object(v___x_1153_);
lean_dec(v_i_1148_);
v___x_1155_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1155_;
}
case 8:
{
lean_object* v___x_1156_; 
lean_del_object(v___x_1153_);
lean_dec(v_i_1148_);
v___x_1156_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1156_;
}
case 10:
{
lean_object* v_types_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_types_1157_ = lean_ctor_get(v_a_1151_, 1);
lean_inc_ref(v_types_1157_);
lean_dec_ref_known(v_a_1151_, 2);
v___x_1158_ = lean_array_get_size(v_types_1157_);
v___x_1159_ = lean_nat_dec_lt(v_i_1148_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec_ref(v_types_1157_);
lean_del_object(v___x_1153_);
lean_dec(v_i_1148_);
lean_dec(v_ty_1078_);
v___x_1160_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1161_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1160_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_array_fget(v_types_1157_, v_i_1148_);
lean_dec(v_i_1148_);
lean_dec_ref(v_types_1157_);
v___x_1163_ = l_Lean_IR_instBEqIRType_beq(v___x_1162_, v_ty_1078_);
lean_dec(v_ty_1078_);
lean_dec(v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_del_object(v___x_1153_);
v___x_1164_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1165_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1164_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1166_);
v___x_1168_ = v___x_1153_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
case 11:
{
lean_object* v_types_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_types_1170_ = lean_ctor_get(v_a_1151_, 1);
lean_inc_ref(v_types_1170_);
lean_dec_ref_known(v_a_1151_, 2);
v___x_1171_ = lean_array_get_size(v_types_1170_);
v___x_1172_ = lean_nat_dec_lt(v_i_1148_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref(v_types_1170_);
lean_del_object(v___x_1153_);
lean_dec(v_i_1148_);
lean_dec(v_ty_1078_);
v___x_1173_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1174_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1173_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_array_fget(v_types_1170_, v_i_1148_);
lean_dec(v_i_1148_);
lean_dec_ref(v_types_1170_);
v___x_1176_ = l_Lean_IR_instBEqIRType_beq(v___x_1175_, v_ty_1078_);
lean_dec(v_ty_1078_);
lean_dec(v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_del_object(v___x_1153_);
v___x_1177_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1178_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1177_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1179_);
v___x_1181_ = v___x_1153_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
case 12:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_i_1148_);
lean_dec(v_ty_1078_);
v___x_1183_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1183_);
v___x_1185_ = v___x_1153_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
default: 
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_del_object(v___x_1153_);
lean_dec(v_i_1148_);
lean_dec(v_ty_1078_);
v___x_1187_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1188_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1151_);
v___x_1189_ = l_Std_Format_defWidth;
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = l_Std_Format_pretty(v___x_1188_, v___x_1189_, v___x_1190_, v___x_1190_);
v___x_1192_ = lean_string_append(v___x_1187_, v___x_1191_);
lean_dec_ref(v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1194_ = lean_string_append(v___x_1192_, v___x_1193_);
v___x_1195_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1194_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_i_1148_);
lean_dec(v_ty_1078_);
v_a_1197_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1150_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1150_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
case 4:
{
lean_object* v_x_1205_; lean_object* v___x_1206_; 
v_x_1205_ = lean_ctor_get(v_e_1079_, 1);
lean_inc(v_x_1205_);
lean_dec_ref_known(v_e_1079_, 2);
v___x_1206_ = l_Lean_IR_Checker_checkObjVar(v_x_1205_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1225_; 
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1206_, 0);
lean_dec(v_unused_1226_);
v___x_1208_ = v___x_1206_;
v_isShared_1209_ = v_isSharedCheck_1225_;
goto v_resetjp_1207_;
}
else
{
lean_dec(v___x_1206_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1225_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_box(5);
v___x_1211_ = l_Lean_IR_instBEqIRType_beq(v_ty_1078_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_msg_1219_; lean_object* v___x_1220_; 
lean_del_object(v___x_1208_);
v___x_1212_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1213_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1078_);
v___x_1214_ = l_Std_Format_defWidth;
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = l_Std_Format_pretty(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1215_);
v___x_1217_ = lean_string_append(v___x_1212_, v___x_1216_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
v___x_1220_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1219_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
lean_dec(v_ty_1078_);
v___x_1221_ = lean_box(0);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1221_);
v___x_1223_ = v___x_1208_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_dec(v_ty_1078_);
return v___x_1206_;
}
}
case 5:
{
lean_object* v_x_1227_; lean_object* v___x_1228_; 
v_x_1227_ = lean_ctor_get(v_e_1079_, 2);
lean_inc(v_x_1227_);
lean_dec_ref_known(v_e_1079_, 3);
v___x_1228_ = l_Lean_IR_Checker_checkObjVar(v_x_1227_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref_known(v___x_1228_, 1);
v___x_1229_ = l_Lean_IR_Checker_checkScalarType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1229_;
}
else
{
lean_dec(v_ty_1078_);
return v___x_1228_;
}
}
case 6:
{
lean_object* v_c_1230_; lean_object* v_ys_1231_; lean_object* v___x_1232_; 
lean_dec(v_ty_1078_);
v_c_1230_ = lean_ctor_get(v_e_1079_, 0);
lean_inc(v_c_1230_);
v_ys_1231_ = lean_ctor_get(v_e_1079_, 1);
lean_inc_ref(v_ys_1231_);
lean_dec_ref_known(v_e_1079_, 2);
v___x_1232_ = l_Lean_IR_Checker_checkFullApp(v_c_1230_, v_ys_1231_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec_ref(v_ys_1231_);
return v___x_1232_;
}
case 7:
{
lean_object* v_c_1233_; lean_object* v_ys_1234_; lean_object* v___x_1235_; 
v_c_1233_ = lean_ctor_get(v_e_1079_, 0);
lean_inc(v_c_1233_);
v_ys_1234_ = lean_ctor_get(v_e_1079_, 1);
lean_inc_ref(v_ys_1234_);
lean_dec_ref_known(v_e_1079_, 2);
v___x_1235_ = l_Lean_IR_Checker_checkPartialApp(v_c_1233_, v_ys_1234_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec_ref(v_ys_1234_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref_known(v___x_1235_, 1);
v___x_1236_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1236_;
}
else
{
lean_dec(v_ty_1078_);
return v___x_1235_;
}
}
case 8:
{
lean_object* v_x_1237_; lean_object* v_ys_1238_; lean_object* v___x_1239_; 
v_x_1237_ = lean_ctor_get(v_e_1079_, 0);
lean_inc(v_x_1237_);
v_ys_1238_ = lean_ctor_get(v_e_1079_, 1);
lean_inc_ref(v_ys_1238_);
lean_dec_ref_known(v_e_1079_, 2);
v___x_1239_ = l_Lean_IR_Checker_checkObjVar(v_x_1237_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref_known(v___x_1239_, 1);
v___x_1240_ = l_Lean_IR_Checker_checkArgs(v_ys_1238_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec_ref(v_ys_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1240_, 1);
v___x_1241_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1241_;
}
else
{
lean_dec(v_ty_1078_);
return v___x_1240_;
}
}
else
{
lean_dec_ref(v_ys_1238_);
lean_dec(v_ty_1078_);
return v___x_1239_;
}
}
case 9:
{
lean_object* v_ty_1242_; lean_object* v_x_1243_; lean_object* v___x_1244_; 
v_ty_1242_ = lean_ctor_get(v_e_1079_, 0);
lean_inc(v_ty_1242_);
v_x_1243_ = lean_ctor_get(v_e_1079_, 1);
lean_inc(v_x_1243_);
lean_dec_ref_known(v_e_1079_, 2);
v___x_1244_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; 
lean_dec_ref_known(v___x_1244_, 1);
lean_inc(v_x_1243_);
v___x_1245_ = l_Lean_IR_Checker_checkScalarVar(v_x_1243_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref_known(v___x_1245_, 1);
v___x_1246_ = l_Lean_IR_Checker_getType(v_x_1243_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1265_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1265_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1265_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Lean_IR_instBEqIRType_beq(v_a_1247_, v_ty_1242_);
lean_dec(v_ty_1242_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_msg_1259_; lean_object* v___x_1260_; 
lean_del_object(v___x_1249_);
v___x_1252_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1253_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1247_);
v___x_1254_ = l_Std_Format_defWidth;
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = l_Std_Format_pretty(v___x_1253_, v___x_1254_, v___x_1255_, v___x_1255_);
v___x_1257_ = lean_string_append(v___x_1252_, v___x_1256_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
v___x_1260_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1259_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
lean_dec(v_a_1247_);
v___x_1261_ = lean_box(0);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1261_);
v___x_1263_ = v___x_1249_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_ty_1242_);
v_a_1266_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1246_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1246_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_dec(v_x_1243_);
lean_dec(v_ty_1242_);
return v___x_1245_;
}
}
else
{
lean_dec(v_x_1243_);
lean_dec(v_ty_1242_);
return v___x_1244_;
}
}
case 10:
{
lean_object* v_x_1274_; lean_object* v___x_1275_; 
v_x_1274_ = lean_ctor_get(v_e_1079_, 0);
lean_inc(v_x_1274_);
lean_dec_ref_known(v_e_1079_, 1);
v___x_1275_ = l_Lean_IR_Checker_checkScalarType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref_known(v___x_1275_, 1);
v___x_1276_ = l_Lean_IR_Checker_checkObjVar(v_x_1274_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1276_;
}
else
{
lean_dec(v_x_1274_);
return v___x_1275_;
}
}
case 11:
{
lean_object* v_v_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1286_; 
v_v_1277_ = lean_ctor_get(v_e_1079_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_e_1079_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1279_ = v_e_1079_;
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_v_1277_);
lean_dec(v_e_1079_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
if (lean_obj_tag(v_v_1277_) == 1)
{
lean_object* v___x_1281_; 
lean_dec_ref_known(v_v_1277_, 1);
lean_del_object(v___x_1279_);
v___x_1281_ = l_Lean_IR_Checker_checkObjType(v_ty_1078_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
lean_dec_ref(v_v_1277_);
lean_dec(v_ty_1078_);
v___x_1282_ = lean_box(0);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
default: 
{
lean_object* v_x_1287_; lean_object* v___x_1288_; 
v_x_1287_ = lean_ctor_get(v_e_1079_, 0);
lean_inc(v_x_1287_);
lean_dec_ref_known(v_e_1079_, 1);
v___x_1288_ = l_Lean_IR_Checker_checkObjVar(v_x_1287_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1307_; 
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; 
v_unused_1308_ = lean_ctor_get(v___x_1288_, 0);
lean_dec(v_unused_1308_);
v___x_1290_ = v___x_1288_;
v_isShared_1291_ = v_isSharedCheck_1307_;
goto v_resetjp_1289_;
}
else
{
lean_dec(v___x_1288_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1307_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_box(1);
v___x_1293_ = l_Lean_IR_instBEqIRType_beq(v_ty_1078_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_msg_1301_; lean_object* v___x_1302_; 
lean_del_object(v___x_1290_);
v___x_1294_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1295_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1078_);
v___x_1296_ = l_Std_Format_defWidth;
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = l_Std_Format_pretty(v___x_1295_, v___x_1296_, v___x_1297_, v___x_1297_);
v___x_1299_ = lean_string_append(v___x_1294_, v___x_1298_);
lean_dec_ref(v___x_1298_);
v___x_1300_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1301_ = lean_string_append(v___x_1299_, v___x_1300_);
v___x_1302_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1301_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_dec(v_ty_1078_);
v___x_1303_ = lean_box(0);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1303_);
v___x_1305_ = v___x_1290_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_dec(v_ty_1078_);
return v___x_1288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1309_, lean_object* v_e_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_IR_Checker_checkExpr(v_ty_1309_, v_e_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1317_, lean_object* v_p_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_x_1324_; lean_object* v___x_1325_; 
v_x_1324_ = lean_ctor_get(v_p_1318_, 0);
lean_inc(v_x_1324_);
v___x_1325_ = l_Lean_IR_Checker_markVar(v_x_1324_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v___x_1325_, 0);
lean_dec(v_unused_1334_);
v___x_1327_ = v___x_1325_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v___x_1325_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = l_Lean_IR_LocalContext_addParam(v_ctx_1317_, v_p_1318_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1329_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_p_1318_);
lean_dec_ref(v_ctx_1317_);
v_a_1335_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1325_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1325_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1343_, lean_object* v_p_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1343_, v_p_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1350_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_instMonadEIO___redArg();
return v___x_1351_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1353_ = l_StateRefT_x27_instMonad___redArg(v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1357_, lean_object* v_k_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v_toApplicative_1365_; lean_object* v_toFunctor_1366_; lean_object* v_toSeq_1367_; lean_object* v_toSeqLeft_1368_; lean_object* v_toSeqRight_1369_; lean_object* v___f_1370_; lean_object* v___f_1371_; lean_object* v___f_1372_; lean_object* v___f_1373_; lean_object* v___x_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_localCtx_1382_; lean_object* v_currentDecl_1383_; lean_object* v_decls_1384_; lean_object* v_a_1386_; lean_object* v___y_1390_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1364_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1365_ = lean_ctor_get(v___x_1364_, 0);
v_toFunctor_1366_ = lean_ctor_get(v_toApplicative_1365_, 0);
v_toSeq_1367_ = lean_ctor_get(v_toApplicative_1365_, 2);
v_toSeqLeft_1368_ = lean_ctor_get(v_toApplicative_1365_, 3);
v_toSeqRight_1369_ = lean_ctor_get(v_toApplicative_1365_, 4);
v___f_1370_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1371_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1366_, 2);
v___f_1372_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1372_, 0, v_toFunctor_1366_);
v___f_1373_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1373_, 0, v_toFunctor_1366_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___f_1372_);
lean_ctor_set(v___x_1374_, 1, v___f_1373_);
lean_inc(v_toSeqRight_1369_);
v___f_1375_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1375_, 0, v_toSeqRight_1369_);
lean_inc(v_toSeqLeft_1368_);
v___f_1376_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1376_, 0, v_toSeqLeft_1368_);
lean_inc(v_toSeq_1367_);
v___f_1377_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1377_, 0, v_toSeq_1367_);
v___x_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1374_);
lean_ctor_set(v___x_1378_, 1, v___f_1370_);
lean_ctor_set(v___x_1378_, 2, v___f_1377_);
lean_ctor_set(v___x_1378_, 3, v___f_1376_);
lean_ctor_set(v___x_1378_, 4, v___f_1375_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___f_1371_);
v___x_1380_ = l_StateRefT_x27_instMonad___redArg(v___x_1379_);
v___x_1381_ = l_ReaderT_instMonad___redArg(v___x_1380_);
v_localCtx_1382_ = lean_ctor_get(v_a_1359_, 0);
v_currentDecl_1383_ = lean_ctor_get(v_a_1359_, 1);
v_decls_1384_ = lean_ctor_get(v_a_1359_, 2);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_array_get_size(v_ps_1357_);
v___x_1402_ = lean_nat_dec_lt(v___x_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_dec_ref(v___x_1381_);
lean_dec_ref(v_ps_1357_);
lean_inc_ref(v_localCtx_1382_);
v_a_1386_ = v_localCtx_1382_;
goto v___jp_1385_;
}
else
{
lean_object* v___f_1403_; uint8_t v___x_1404_; 
v___f_1403_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1404_ = lean_nat_dec_le(v___x_1401_, v___x_1401_);
if (v___x_1404_ == 0)
{
if (v___x_1402_ == 0)
{
lean_dec_ref(v___x_1381_);
lean_dec_ref(v_ps_1357_);
lean_inc_ref(v_localCtx_1382_);
v_a_1386_ = v_localCtx_1382_;
goto v___jp_1385_;
}
else
{
size_t v___x_1405_; size_t v___x_1406_; lean_object* v___x_1038__overap_1407_; lean_object* v___x_1408_; 
v___x_1405_ = ((size_t)0ULL);
v___x_1406_ = lean_usize_of_nat(v___x_1401_);
lean_inc_ref(v_localCtx_1382_);
v___x_1038__overap_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1381_, v___f_1403_, v_ps_1357_, v___x_1405_, v___x_1406_, v_localCtx_1382_);
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v_a_1360_);
lean_inc_ref(v_a_1359_);
v___x_1408_ = lean_apply_5(v___x_1038__overap_1407_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, lean_box(0));
v___y_1390_ = v___x_1408_;
goto v___jp_1389_;
}
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1042__overap_1411_; lean_object* v___x_1412_; 
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1401_);
lean_inc_ref(v_localCtx_1382_);
v___x_1042__overap_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1381_, v___f_1403_, v_ps_1357_, v___x_1409_, v___x_1410_, v_localCtx_1382_);
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v_a_1360_);
lean_inc_ref(v_a_1359_);
v___x_1412_ = lean_apply_5(v___x_1042__overap_1411_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, lean_box(0));
v___y_1390_ = v___x_1412_;
goto v___jp_1389_;
}
}
v___jp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_inc_ref(v_decls_1384_);
lean_inc_ref(v_currentDecl_1383_);
v___x_1387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1387_, 0, v_a_1386_);
lean_ctor_set(v___x_1387_, 1, v_currentDecl_1383_);
lean_ctor_set(v___x_1387_, 2, v_decls_1384_);
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v_a_1360_);
v___x_1388_ = lean_apply_5(v_k_1358_, v___x_1387_, v_a_1360_, v_a_1361_, v_a_1362_, lean_box(0));
return v___x_1388_;
}
v___jp_1389_:
{
if (lean_obj_tag(v___y_1390_) == 0)
{
lean_object* v_a_1391_; 
v_a_1391_ = lean_ctor_get(v___y_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___y_1390_, 1);
v_a_1386_ = v_a_1391_;
goto v___jp_1385_;
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v_k_1358_);
v_a_1392_ = lean_ctor_get(v___y_1390_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___y_1390_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___y_1390_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___y_1390_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1413_, lean_object* v_k_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_IR_Checker_withParams(v_ps_1413_, v_k_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1421_, size_t v_i_1422_, size_t v_stop_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_usize_dec_eq(v_i_1422_, v_stop_1423_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v_x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_array_uget_borrowed(v_as_1421_, v_i_1422_);
v_x_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_x_1432_);
v___x_1433_ = l_Lean_IR_Checker_markVar(v_x_1432_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; 
lean_dec_ref_known(v___x_1433_, 1);
lean_inc(v___x_1431_);
v___x_1434_ = l_Lean_IR_LocalContext_addParam(v_b_1424_, v___x_1431_);
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = lean_usize_add(v_i_1422_, v___x_1435_);
v_i_1422_ = v___x_1436_;
v_b_1424_ = v___x_1434_;
goto _start;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_b_1424_);
v_a_1438_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1433_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1433_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1424_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1447_, lean_object* v_i_1448_, lean_object* v_stop_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
size_t v_i_boxed_1456_; size_t v_stop_boxed_1457_; lean_object* v_res_1458_; 
v_i_boxed_1456_ = lean_unbox_usize(v_i_1448_);
lean_dec(v_i_1448_);
v_stop_boxed_1457_ = lean_unbox_usize(v_stop_1449_);
lean_dec(v_stop_1449_);
v_res_1458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1447_, v_i_boxed_1456_, v_stop_boxed_1457_, v_b_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec_ref(v_as_1447_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v_x_1466_; lean_object* v_b_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; 
switch(lean_obj_tag(v_fnBody_1459_))
{
case 0:
{
lean_object* v_x_1474_; lean_object* v_ty_1475_; lean_object* v_e_1476_; lean_object* v_b_1477_; lean_object* v___x_1478_; 
v_x_1474_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_x_1474_);
v_ty_1475_ = lean_ctor_get(v_fnBody_1459_, 1);
lean_inc_n(v_ty_1475_, 2);
v_e_1476_ = lean_ctor_get(v_fnBody_1459_, 2);
lean_inc_ref_n(v_e_1476_, 2);
v_b_1477_ = lean_ctor_get(v_fnBody_1459_, 3);
lean_inc(v_b_1477_);
lean_dec_ref_known(v_fnBody_1459_, 4);
v___x_1478_ = l_Lean_IR_Checker_checkExpr(v_ty_1475_, v_e_1476_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref_known(v___x_1478_, 1);
lean_inc(v_x_1474_);
v___x_1479_ = l_Lean_IR_Checker_markVar(v_x_1474_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_localCtx_1480_; lean_object* v_currentDecl_1481_; lean_object* v_decls_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref_known(v___x_1479_, 1);
v_localCtx_1480_ = lean_ctor_get(v_a_1460_, 0);
lean_inc_ref(v_localCtx_1480_);
v_currentDecl_1481_ = lean_ctor_get(v_a_1460_, 1);
lean_inc_ref(v_currentDecl_1481_);
v_decls_1482_ = lean_ctor_get(v_a_1460_, 2);
lean_inc_ref(v_decls_1482_);
lean_dec_ref(v_a_1460_);
v___x_1483_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1480_, v_x_1474_, v_ty_1475_, v_e_1476_);
v___x_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v_currentDecl_1481_);
lean_ctor_set(v___x_1484_, 2, v_decls_1482_);
v_fnBody_1459_ = v_b_1477_;
v_a_1460_ = v___x_1484_;
goto _start;
}
else
{
lean_dec(v_b_1477_);
lean_dec_ref(v_e_1476_);
lean_dec(v_ty_1475_);
lean_dec(v_x_1474_);
lean_dec_ref(v_a_1460_);
return v___x_1479_;
}
}
else
{
lean_dec(v_b_1477_);
lean_dec_ref(v_e_1476_);
lean_dec(v_ty_1475_);
lean_dec(v_x_1474_);
lean_dec_ref(v_a_1460_);
return v___x_1478_;
}
}
case 1:
{
lean_object* v_j_1486_; lean_object* v_xs_1487_; lean_object* v_v_1488_; lean_object* v_b_1489_; lean_object* v_a_1491_; lean_object* v___x_1500_; 
v_j_1486_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc_n(v_j_1486_, 2);
v_xs_1487_ = lean_ctor_get(v_fnBody_1459_, 1);
lean_inc_ref(v_xs_1487_);
v_v_1488_ = lean_ctor_get(v_fnBody_1459_, 2);
lean_inc(v_v_1488_);
v_b_1489_ = lean_ctor_get(v_fnBody_1459_, 3);
lean_inc(v_b_1489_);
lean_dec_ref_known(v_fnBody_1459_, 4);
v___x_1500_ = l_Lean_IR_Checker_markJP(v_j_1486_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_localCtx_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
lean_dec_ref_known(v___x_1500_, 1);
v_localCtx_1501_ = lean_ctor_get(v_a_1460_, 0);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = lean_array_get_size(v_xs_1487_);
v___x_1504_ = lean_nat_dec_lt(v___x_1502_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_inc_ref(v_localCtx_1501_);
v_a_1491_ = v_localCtx_1501_;
goto v___jp_1490_;
}
else
{
size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = ((size_t)0ULL);
v___x_1506_ = lean_usize_of_nat(v___x_1503_);
lean_inc_ref(v_localCtx_1501_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1487_, v___x_1505_, v___x_1506_, v_localCtx_1501_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
v_a_1491_ = v_a_1508_;
goto v___jp_1490_;
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_b_1489_);
lean_dec(v_v_1488_);
lean_dec_ref(v_xs_1487_);
lean_dec(v_j_1486_);
lean_dec_ref(v_a_1460_);
v_a_1509_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1507_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1507_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
else
{
lean_dec(v_b_1489_);
lean_dec(v_v_1488_);
lean_dec_ref(v_xs_1487_);
lean_dec(v_j_1486_);
lean_dec_ref(v_a_1460_);
return v___x_1500_;
}
v___jp_1490_:
{
lean_object* v_localCtx_1492_; lean_object* v_currentDecl_1493_; lean_object* v_decls_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_localCtx_1492_ = lean_ctor_get(v_a_1460_, 0);
lean_inc_ref(v_localCtx_1492_);
v_currentDecl_1493_ = lean_ctor_get(v_a_1460_, 1);
lean_inc_ref_n(v_currentDecl_1493_, 2);
v_decls_1494_ = lean_ctor_get(v_a_1460_, 2);
lean_inc_ref_n(v_decls_1494_, 2);
lean_dec_ref(v_a_1460_);
v___x_1495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1495_, 0, v_a_1491_);
lean_ctor_set(v___x_1495_, 1, v_currentDecl_1493_);
lean_ctor_set(v___x_1495_, 2, v_decls_1494_);
lean_inc(v_v_1488_);
v___x_1496_ = l_Lean_IR_Checker_checkFnBody(v_v_1488_, v___x_1495_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec_ref_known(v___x_1496_, 1);
v___x_1497_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1492_, v_j_1486_, v_xs_1487_, v_v_1488_);
v___x_1498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v_currentDecl_1493_);
lean_ctor_set(v___x_1498_, 2, v_decls_1494_);
v_fnBody_1459_ = v_b_1489_;
v_a_1460_ = v___x_1498_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1494_);
lean_dec_ref(v_currentDecl_1493_);
lean_dec_ref(v_localCtx_1492_);
lean_dec(v_b_1489_);
lean_dec(v_v_1488_);
lean_dec_ref(v_xs_1487_);
lean_dec(v_j_1486_);
return v___x_1496_;
}
}
}
case 2:
{
lean_object* v_x_1517_; lean_object* v_y_1518_; lean_object* v_b_1519_; lean_object* v___x_1520_; 
v_x_1517_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_x_1517_);
v_y_1518_ = lean_ctor_get(v_fnBody_1459_, 2);
lean_inc(v_y_1518_);
v_b_1519_ = lean_ctor_get(v_fnBody_1459_, 3);
lean_inc(v_b_1519_);
lean_dec_ref_known(v_fnBody_1459_, 4);
v___x_1520_ = l_Lean_IR_Checker_checkVar(v_x_1517_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1521_; 
lean_dec_ref_known(v___x_1520_, 1);
v___x_1521_ = l_Lean_IR_Checker_checkArg(v_y_1518_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_dec_ref_known(v___x_1521_, 1);
v_fnBody_1459_ = v_b_1519_;
goto _start;
}
else
{
lean_dec(v_b_1519_);
lean_dec_ref(v_a_1460_);
return v___x_1521_;
}
}
else
{
lean_dec(v_b_1519_);
lean_dec(v_y_1518_);
lean_dec_ref(v_a_1460_);
return v___x_1520_;
}
}
case 3:
{
lean_object* v_x_1523_; lean_object* v_b_1524_; lean_object* v___x_1525_; 
v_x_1523_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_x_1523_);
v_b_1524_ = lean_ctor_get(v_fnBody_1459_, 2);
lean_inc(v_b_1524_);
lean_dec_ref_known(v_fnBody_1459_, 3);
v___x_1525_ = l_Lean_IR_Checker_checkVar(v_x_1523_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_dec_ref_known(v___x_1525_, 1);
v_fnBody_1459_ = v_b_1524_;
goto _start;
}
else
{
lean_dec(v_b_1524_);
lean_dec_ref(v_a_1460_);
return v___x_1525_;
}
}
case 4:
{
lean_object* v_x_1527_; lean_object* v_y_1528_; lean_object* v_b_1529_; lean_object* v___x_1530_; 
v_x_1527_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_x_1527_);
v_y_1528_ = lean_ctor_get(v_fnBody_1459_, 2);
lean_inc(v_y_1528_);
v_b_1529_ = lean_ctor_get(v_fnBody_1459_, 3);
lean_inc(v_b_1529_);
lean_dec_ref_known(v_fnBody_1459_, 4);
v___x_1530_ = l_Lean_IR_Checker_checkVar(v_x_1527_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1531_; 
lean_dec_ref_known(v___x_1530_, 1);
v___x_1531_ = l_Lean_IR_Checker_checkVar(v_y_1528_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_dec_ref_known(v___x_1531_, 1);
v_fnBody_1459_ = v_b_1529_;
goto _start;
}
else
{
lean_dec(v_b_1529_);
lean_dec_ref(v_a_1460_);
return v___x_1531_;
}
}
else
{
lean_dec(v_b_1529_);
lean_dec(v_y_1528_);
lean_dec_ref(v_a_1460_);
return v___x_1530_;
}
}
case 5:
{
lean_object* v_x_1533_; lean_object* v_y_1534_; lean_object* v_b_1535_; lean_object* v___x_1536_; 
v_x_1533_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_x_1533_);
v_y_1534_ = lean_ctor_get(v_fnBody_1459_, 3);
lean_inc(v_y_1534_);
v_b_1535_ = lean_ctor_get(v_fnBody_1459_, 5);
lean_inc(v_b_1535_);
lean_dec_ref_known(v_fnBody_1459_, 6);
v___x_1536_ = l_Lean_IR_Checker_checkVar(v_x_1533_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1537_; 
lean_dec_ref_known(v___x_1536_, 1);
v___x_1537_ = l_Lean_IR_Checker_checkVar(v_y_1534_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_dec_ref_known(v___x_1537_, 1);
v_fnBody_1459_ = v_b_1535_;
goto _start;
}
else
{
lean_dec(v_b_1535_);
lean_dec_ref(v_a_1460_);
return v___x_1537_;
}
}
else
{
lean_dec(v_b_1535_);
lean_dec(v_y_1534_);
lean_dec_ref(v_a_1460_);
return v___x_1536_;
}
}
case 8:
{
lean_object* v_x_1539_; lean_object* v_b_1540_; lean_object* v___x_1541_; 
v_x_1539_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_x_1539_);
v_b_1540_ = lean_ctor_get(v_fnBody_1459_, 1);
lean_inc(v_b_1540_);
lean_dec_ref_known(v_fnBody_1459_, 2);
v___x_1541_ = l_Lean_IR_Checker_checkVar(v_x_1539_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_dec_ref_known(v___x_1541_, 1);
v_fnBody_1459_ = v_b_1540_;
goto _start;
}
else
{
lean_dec(v_b_1540_);
lean_dec_ref(v_a_1460_);
return v___x_1541_;
}
}
case 9:
{
lean_object* v_x_1543_; lean_object* v_cs_1544_; lean_object* v___x_1545_; 
v_x_1543_ = lean_ctor_get(v_fnBody_1459_, 1);
lean_inc(v_x_1543_);
v_cs_1544_ = lean_ctor_get(v_fnBody_1459_, 3);
lean_inc_ref(v_cs_1544_);
lean_dec_ref_known(v_fnBody_1459_, 4);
v___x_1545_ = l_Lean_IR_Checker_checkVar(v_x_1543_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1566_; 
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v___x_1545_, 0);
lean_dec(v_unused_1567_);
v___x_1547_ = v___x_1545_;
v_isShared_1548_ = v_isSharedCheck_1566_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v___x_1545_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1566_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = lean_array_get_size(v_cs_1544_);
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_nat_dec_lt(v___x_1549_, v___x_1550_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1554_; 
lean_dec_ref(v_cs_1544_);
lean_dec_ref(v_a_1460_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1551_);
v___x_1554_ = v___x_1547_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1551_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
uint8_t v___x_1556_; 
v___x_1556_ = lean_nat_dec_le(v___x_1550_, v___x_1550_);
if (v___x_1556_ == 0)
{
if (v___x_1552_ == 0)
{
lean_object* v___x_1558_; 
lean_dec_ref(v_cs_1544_);
lean_dec_ref(v_a_1460_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1551_);
v___x_1558_ = v___x_1547_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1551_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
else
{
size_t v___x_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
lean_del_object(v___x_1547_);
v___x_1560_ = ((size_t)0ULL);
v___x_1561_ = lean_usize_of_nat(v___x_1550_);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1544_, v___x_1560_, v___x_1561_, v___x_1551_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec_ref(v_a_1460_);
lean_dec_ref(v_cs_1544_);
return v___x_1562_;
}
}
else
{
size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
lean_del_object(v___x_1547_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = lean_usize_of_nat(v___x_1550_);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1544_, v___x_1563_, v___x_1564_, v___x_1551_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec_ref(v_a_1460_);
lean_dec_ref(v_cs_1544_);
return v___x_1565_;
}
}
}
}
else
{
lean_dec_ref(v_cs_1544_);
lean_dec_ref(v_a_1460_);
return v___x_1545_;
}
}
case 10:
{
lean_object* v_x_1568_; lean_object* v___x_1569_; 
v_x_1568_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_x_1568_);
lean_dec_ref_known(v_fnBody_1459_, 1);
v___x_1569_ = l_Lean_IR_Checker_checkArg(v_x_1568_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec_ref(v_a_1460_);
return v___x_1569_;
}
case 11:
{
lean_object* v_j_1570_; lean_object* v_ys_1571_; lean_object* v___x_1572_; 
v_j_1570_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_j_1570_);
v_ys_1571_ = lean_ctor_get(v_fnBody_1459_, 1);
lean_inc_ref(v_ys_1571_);
lean_dec_ref_known(v_fnBody_1459_, 2);
v___x_1572_ = l_Lean_IR_Checker_checkJP(v_j_1570_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1572_, 1);
v___x_1573_ = l_Lean_IR_Checker_checkArgs(v_ys_1571_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec_ref(v_a_1460_);
lean_dec_ref(v_ys_1571_);
return v___x_1573_;
}
else
{
lean_dec_ref(v_ys_1571_);
lean_dec_ref(v_a_1460_);
return v___x_1572_;
}
}
case 12:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec_ref(v_a_1460_);
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
default: 
{
lean_object* v_x_1576_; lean_object* v_b_1577_; 
v_x_1576_ = lean_ctor_get(v_fnBody_1459_, 0);
lean_inc(v_x_1576_);
v_b_1577_ = lean_ctor_get(v_fnBody_1459_, 2);
lean_inc(v_b_1577_);
lean_dec(v_fnBody_1459_);
v_x_1466_ = v_x_1576_;
v_b_1467_ = v_b_1577_;
v___y_1468_ = v_a_1460_;
v___y_1469_ = v_a_1461_;
v___y_1470_ = v_a_1462_;
v___y_1471_ = v_a_1463_;
goto v___jp_1465_;
}
}
v___jp_1465_:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_IR_Checker_checkVar(v_x_1466_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_dec_ref_known(v___x_1472_, 1);
v_fnBody_1459_ = v_b_1467_;
v_a_1460_ = v___y_1468_;
v_a_1461_ = v___y_1469_;
v_a_1462_ = v___y_1470_;
v_a_1463_ = v___y_1471_;
goto _start;
}
else
{
lean_dec_ref(v___y_1468_);
lean_dec(v_b_1467_);
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1578_, size_t v_i_1579_, size_t v_stop_1580_, lean_object* v_b_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v___x_1587_; 
v___x_1587_ = lean_usize_dec_eq(v_i_1579_, v_stop_1580_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = lean_array_uget_borrowed(v_as_1578_, v_i_1579_);
v___x_1589_ = l_Lean_IR_Alt_body(v___x_1588_);
lean_inc_ref(v___y_1582_);
v___x_1590_ = l_Lean_IR_Checker_checkFnBody(v___x_1589_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; size_t v___x_1592_; size_t v___x_1593_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = ((size_t)1ULL);
v___x_1593_ = lean_usize_add(v_i_1579_, v___x_1592_);
v_i_1579_ = v___x_1593_;
v_b_1581_ = v_a_1591_;
goto _start;
}
else
{
return v___x_1590_;
}
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_b_1581_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1596_, lean_object* v_i_1597_, lean_object* v_stop_1598_, lean_object* v_b_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
size_t v_i_boxed_1605_; size_t v_stop_boxed_1606_; lean_object* v_res_1607_; 
v_i_boxed_1605_ = lean_unbox_usize(v_i_1597_);
lean_dec(v_i_1597_);
v_stop_boxed_1606_ = lean_unbox_usize(v_stop_1598_);
lean_dec(v_stop_1598_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1596_, v_i_boxed_1605_, v_stop_boxed_1606_, v_b_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v_as_1596_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
if (lean_obj_tag(v_x_1615_) == 0)
{
lean_object* v_xs_1621_; lean_object* v_body_1622_; lean_object* v_localCtx_1623_; lean_object* v_currentDecl_1624_; lean_object* v_decls_1625_; lean_object* v_a_1627_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v_xs_1621_ = lean_ctor_get(v_x_1615_, 1);
lean_inc_ref(v_xs_1621_);
v_body_1622_ = lean_ctor_get(v_x_1615_, 3);
lean_inc(v_body_1622_);
lean_dec_ref_known(v_x_1615_, 5);
v_localCtx_1623_ = lean_ctor_get(v_a_1616_, 0);
v_currentDecl_1624_ = lean_ctor_get(v_a_1616_, 1);
v_decls_1625_ = lean_ctor_get(v_a_1616_, 2);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_array_get_size(v_xs_1621_);
v___x_1632_ = lean_nat_dec_lt(v___x_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_dec_ref(v_xs_1621_);
lean_inc_ref(v_localCtx_1623_);
v_a_1627_ = v_localCtx_1623_;
goto v___jp_1626_;
}
else
{
size_t v___x_1633_; size_t v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = ((size_t)0ULL);
v___x_1634_ = lean_usize_of_nat(v___x_1631_);
lean_inc_ref(v_localCtx_1623_);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1621_, v___x_1633_, v___x_1634_, v_localCtx_1623_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
lean_dec_ref(v_xs_1621_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v_a_1627_ = v_a_1636_;
goto v___jp_1626_;
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_body_1622_);
v_a_1637_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1635_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1635_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_inc_ref(v_decls_1625_);
lean_inc_ref(v_currentDecl_1624_);
v___x_1628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1628_, 0, v_a_1627_);
lean_ctor_set(v___x_1628_, 1, v_currentDecl_1624_);
lean_ctor_set(v___x_1628_, 2, v_decls_1625_);
v___x_1629_ = l_Lean_IR_Checker_checkFnBody(v_body_1622_, v___x_1628_, v_a_1617_, v_a_1618_, v_a_1619_);
return v___x_1629_;
}
}
else
{
lean_object* v_xs_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v_xs_1645_ = lean_ctor_get(v_x_1615_, 1);
lean_inc_ref(v_xs_1645_);
lean_dec_ref_known(v_x_1615_, 4);
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = lean_array_get_size(v_xs_1645_);
v___x_1649_ = lean_nat_dec_lt(v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_dec_ref(v_xs_1645_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1646_);
return v___x_1650_;
}
else
{
lean_object* v_localCtx_1651_; size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
v_localCtx_1651_ = lean_ctor_get(v_a_1616_, 0);
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = lean_usize_of_nat(v___x_1648_);
lean_inc_ref(v_localCtx_1651_);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1645_, v___x_1652_, v___x_1653_, v_localCtx_1651_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
lean_dec_ref(v_xs_1645_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v___x_1654_, 0);
lean_dec(v_unused_1662_);
v___x_1656_ = v___x_1654_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_dec(v___x_1654_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1646_);
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1646_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1654_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1654_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_IR_Checker_checkDecl(v_x_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_1682_, lean_object* v_decl_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1687_ = ((lean_object*)(l_Lean_IR_checkDecl___closed__0));
lean_inc_ref(v_decl_1683_);
v___x_1688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v_decl_1683_);
lean_ctor_set(v___x_1688_, 2, v_decls_1682_);
v___x_1689_ = ((lean_object*)(l_Lean_IR_checkDecl___closed__1));
v___x_1690_ = lean_st_mk_ref(v___x_1689_);
v___x_1691_ = l_Lean_IR_Checker_checkDecl(v_decl_1683_, v___x_1688_, v___x_1690_, v_a_1684_, v_a_1685_);
lean_dec_ref_known(v___x_1688_, 3);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1700_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_st_ref_get(v___x_1690_);
lean_dec(v___x_1690_);
lean_dec(v___x_1696_);
if (v_isShared_1695_ == 0)
{
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1692_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_dec(v___x_1690_);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* v_decls_1701_, lean_object* v_decl_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_IR_checkDecl(v_decls_1701_, v_decl_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* v_decls_1707_, lean_object* v_as_1708_, size_t v_i_1709_, size_t v_stop_1710_, lean_object* v_b_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_usize_dec_eq(v_i_1709_, v_stop_1710_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_array_uget_borrowed(v_as_1708_, v_i_1709_);
lean_inc(v___x_1716_);
lean_inc_ref(v_decls_1707_);
v___x_1717_ = l_Lean_IR_checkDecl(v_decls_1707_, v___x_1716_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; size_t v___x_1719_; size_t v___x_1720_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1709_, v___x_1719_);
v_i_1709_ = v___x_1720_;
v_b_1711_ = v_a_1718_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1707_);
return v___x_1717_;
}
}
else
{
lean_object* v___x_1722_; 
lean_dec_ref(v_decls_1707_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_b_1711_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* v_decls_1723_, lean_object* v_as_1724_, lean_object* v_i_1725_, lean_object* v_stop_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
size_t v_i_boxed_1731_; size_t v_stop_boxed_1732_; lean_object* v_res_1733_; 
v_i_boxed_1731_ = lean_unbox_usize(v_i_1725_);
lean_dec(v_i_1725_);
v_stop_boxed_1732_ = lean_unbox_usize(v_stop_1726_);
lean_dec(v_stop_1726_);
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1723_, v_as_1724_, v_i_boxed_1731_, v_stop_boxed_1732_, v_b_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec_ref(v_as_1724_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* v_decls_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = lean_array_get_size(v_decls_1734_);
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_nat_dec_lt(v___x_1738_, v___x_1739_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref(v_decls_1734_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_nat_dec_le(v___x_1739_, v___x_1739_);
if (v___x_1743_ == 0)
{
if (v___x_1741_ == 0)
{
lean_object* v___x_1744_; 
lean_dec_ref(v_decls_1734_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1740_);
return v___x_1744_;
}
else
{
size_t v___x_1745_; size_t v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = lean_usize_of_nat(v___x_1739_);
lean_inc_ref(v_decls_1734_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1734_, v_decls_1734_, v___x_1745_, v___x_1746_, v___x_1740_, v_a_1735_, v_a_1736_);
lean_dec_ref(v_decls_1734_);
return v___x_1747_;
}
}
else
{
size_t v___x_1748_; size_t v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = ((size_t)0ULL);
v___x_1749_ = lean_usize_of_nat(v___x_1739_);
lean_inc_ref(v_decls_1734_);
v___x_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1734_, v_decls_1734_, v___x_1748_, v___x_1749_, v___x_1740_, v_a_1735_, v_a_1736_);
lean_dec_ref(v_decls_1734_);
return v___x_1750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_IR_checkDecls(v_decls_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
return v_res_1755_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Runtime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_Checker(builtin);
}
#ifdef __cplusplus
}
#endif
