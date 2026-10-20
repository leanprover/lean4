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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
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
lean_object* v_localCtx_568_; uint8_t v___x_569_; 
v_localCtx_568_ = lean_ctor_get(v_a_560_, 0);
v___x_569_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_568_, v_x_559_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; 
v___x_570_ = l_Lean_IR_LocalContext_isParam(v_localCtx_568_, v_x_559_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_571_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_572_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_573_ = l_Nat_reprFast(v_x_559_);
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
lean_dec_ref(v___x_573_);
v___x_575_ = lean_string_append(v___x_571_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
v___x_578_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_577_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_578_;
}
else
{
lean_dec(v_x_559_);
goto v___jp_565_;
}
}
else
{
lean_dec(v_x_559_);
goto v___jp_565_;
}
v___jp_565_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_IR_Checker_checkVar(v_x_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_localCtx_594_; uint8_t v___x_595_; 
v_localCtx_594_ = lean_ctor_get(v_a_589_, 0);
v___x_595_ = l_Lean_IR_LocalContext_isJP(v_localCtx_594_, v_j_588_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_596_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_597_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_598_ = l_Nat_reprFast(v_j_588_);
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = lean_string_append(v___x_596_, v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_602_ = lean_string_append(v___x_600_, v___x_601_);
v___x_603_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_602_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v_j_588_);
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_IR_Checker_checkJP(v_j_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
if (lean_obj_tag(v_a_613_) == 0)
{
lean_object* v_id_619_; lean_object* v___x_620_; 
v_id_619_ = lean_ctor_get(v_a_613_, 0);
lean_inc(v_id_619_);
lean_dec_ref_known(v_a_613_, 1);
v___x_620_ = l_Lean_IR_Checker_checkVar(v_id_619_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_box(0);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_IR_Checker_checkArg(v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_630_, size_t v_i_631_, size_t v_stop_632_, lean_object* v_b_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_eq(v_i_631_, v_stop_632_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_array_uget_borrowed(v_as_630_, v_i_631_);
lean_inc(v___x_640_);
v___x_641_ = l_Lean_IR_Checker_checkArg(v___x_640_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; size_t v___x_643_; size_t v___x_644_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_631_, v___x_643_);
v_i_631_ = v___x_644_;
v_b_633_ = v_a_642_;
goto _start;
}
else
{
return v___x_641_;
}
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v_b_633_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_647_, lean_object* v_i_648_, lean_object* v_stop_649_, lean_object* v_b_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
size_t v_i_boxed_656_; size_t v_stop_boxed_657_; lean_object* v_res_658_; 
v_i_boxed_656_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_stop_boxed_657_ = lean_unbox_usize(v_stop_649_);
lean_dec(v_stop_649_);
v_res_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_647_, v_i_boxed_656_, v_stop_boxed_657_, v_b_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v_as_647_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_array_get_size(v_as_659_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_nat_dec_lt(v___x_665_, v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
return v___x_669_;
}
else
{
size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((size_t)0ULL);
v___x_671_ = lean_usize_of_nat(v___x_666_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_659_, v___x_670_, v___x_671_, v___x_667_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_IR_Checker_checkArgs(v_as_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec_ref(v_as_673_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_681_, lean_object* v_ty_u2082_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_681_, v_ty_u2082_682_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_690_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_689_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
return v___x_690_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_box(0);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_693_, lean_object* v_ty_u2082_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_693_, v_ty_u2082_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_ty_u2082_694_);
lean_dec(v_ty_u2081_693_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_703_, lean_object* v_p_704_, lean_object* v_suffix_x3f_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_711_; uint8_t v___x_712_; 
lean_inc(v_ty_703_);
v___x_711_ = lean_apply_1(v_p_704_, v_ty_703_);
v___x_712_ = lean_unbox(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_msg_720_; 
v___x_713_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_714_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_703_);
v___x_715_ = l_Std_Format_defWidth;
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = l_Std_Format_pretty(v___x_714_, v___x_715_, v___x_716_, v___x_716_);
v___x_718_ = lean_string_append(v___x_713_, v___x_717_);
lean_dec_ref(v___x_717_);
v___x_719_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_720_ = lean_string_append(v___x_718_, v___x_719_);
if (lean_obj_tag(v_suffix_x3f_705_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_msg_724_; lean_object* v___x_725_; 
v_val_721_ = lean_ctor_get(v_suffix_x3f_705_, 0);
v___x_722_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_723_ = lean_string_append(v_msg_720_, v___x_722_);
v_msg_724_ = lean_string_append(v___x_723_, v_val_721_);
v___x_725_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_724_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_720_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v_ty_703_);
v___x_727_ = lean_box(0);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_729_, lean_object* v_p_730_, lean_object* v_suffix_x3f_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_IR_Checker_checkType(v_ty_729_, v_p_730_, v_suffix_x3f_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_suffix_x3f_731_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_IR_IRType_isObj(v_ty_739_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_msg_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_msg_757_; lean_object* v___x_758_; 
v___x_746_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_747_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_748_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_739_);
v___x_749_ = l_Std_Format_defWidth;
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = l_Std_Format_pretty(v___x_748_, v___x_749_, v___x_750_, v___x_750_);
v___x_752_ = lean_string_append(v___x_747_, v___x_751_);
lean_dec_ref(v___x_751_);
v___x_753_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_754_ = lean_string_append(v___x_752_, v___x_753_);
v___x_755_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_756_ = lean_string_append(v_msg_754_, v___x_755_);
v_msg_757_ = lean_string_append(v___x_756_, v___x_746_);
v___x_758_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_757_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec(v_ty_739_);
v___x_759_ = lean_box(0);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_IR_Checker_checkObjType(v_ty_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = l_Lean_IR_IRType_isScalar(v_ty_769_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_msg_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_msg_787_; lean_object* v___x_788_; 
v___x_776_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_777_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_778_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_769_);
v___x_779_ = l_Std_Format_defWidth;
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = l_Std_Format_pretty(v___x_778_, v___x_779_, v___x_780_, v___x_780_);
v___x_782_ = lean_string_append(v___x_777_, v___x_781_);
lean_dec_ref(v___x_781_);
v___x_783_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_784_ = lean_string_append(v___x_782_, v___x_783_);
v___x_785_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_786_ = lean_string_append(v_msg_784_, v___x_785_);
v_msg_787_ = lean_string_append(v___x_786_, v___x_776_);
v___x_788_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_787_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v_ty_769_);
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_IR_Checker_checkScalarType(v_ty_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_localCtx_804_; lean_object* v___x_805_; 
v_localCtx_804_ = lean_ctor_get(v_a_799_, 0);
v___x_805_ = l_Lean_IR_LocalContext_getType(v_localCtx_804_, v_x_798_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_806_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_807_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_808_ = l_Nat_reprFast(v_x_798_);
v___x_809_ = lean_string_append(v___x_807_, v___x_808_);
lean_dec_ref(v___x_808_);
v___x_810_ = lean_string_append(v___x_806_, v___x_809_);
lean_dec_ref(v___x_809_);
v___x_811_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_812_ = lean_string_append(v___x_810_, v___x_811_);
v___x_813_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_812_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
return v___x_813_;
}
else
{
lean_object* v_val_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_x_798_);
v_val_814_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_805_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_val_814_);
lean_dec(v___x_805_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 0);
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_val_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_IR_Checker_getType(v_x_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_829_, lean_object* v_p_830_, lean_object* v_suffix_x3f_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_IR_Checker_getType(v_x_829_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_862_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_862_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_862_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_862_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; uint8_t v___x_843_; 
lean_inc(v_a_838_);
v___x_842_ = lean_apply_1(v_p_830_, v_a_838_);
v___x_843_ = lean_unbox(v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_msg_851_; 
lean_del_object(v___x_840_);
v___x_844_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_845_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_838_);
v___x_846_ = l_Std_Format_defWidth;
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = l_Std_Format_pretty(v___x_845_, v___x_846_, v___x_847_, v___x_847_);
v___x_849_ = lean_string_append(v___x_844_, v___x_848_);
lean_dec_ref(v___x_848_);
v___x_850_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_851_ = lean_string_append(v___x_849_, v___x_850_);
if (lean_obj_tag(v_suffix_x3f_831_) == 1)
{
lean_object* v_val_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_msg_855_; lean_object* v___x_856_; 
v_val_852_ = lean_ctor_get(v_suffix_x3f_831_, 0);
v___x_853_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_854_ = lean_string_append(v_msg_851_, v___x_853_);
v_msg_855_ = lean_string_append(v___x_854_, v_val_852_);
v___x_856_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_855_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_851_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
return v___x_857_;
}
}
else
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v_a_838_);
v___x_858_ = lean_box(0);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_858_);
v___x_860_ = v___x_840_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v_p_830_);
v_a_863_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_837_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_837_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_871_, lean_object* v_p_872_, lean_object* v_suffix_x3f_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_IR_Checker_checkVarType(v_x_871_, v_p_872_, v_suffix_x3f_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_suffix_x3f_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_887_ = l_Lean_IR_Checker_getType(v_x_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_909_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_909_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_909_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_909_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_IR_IRType_isObj(v_a_888_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_msg_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_msg_903_; lean_object* v___x_904_; 
lean_del_object(v___x_890_);
v___x_893_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_894_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_888_);
v___x_895_ = l_Std_Format_defWidth;
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = l_Std_Format_pretty(v___x_894_, v___x_895_, v___x_896_, v___x_896_);
v___x_898_ = lean_string_append(v___x_893_, v___x_897_);
lean_dec_ref(v___x_897_);
v___x_899_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_900_ = lean_string_append(v___x_898_, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_902_ = lean_string_append(v_msg_900_, v___x_901_);
v_msg_903_ = lean_string_append(v___x_902_, v___x_886_);
v___x_904_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_903_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_907_; 
lean_dec(v_a_888_);
v___x_905_ = lean_box(0);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_905_);
v___x_907_ = v___x_890_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_a_910_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_887_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_887_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_IR_Checker_checkObjVar(v_x_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_932_ = l_Lean_IR_Checker_getType(v_x_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_954_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_954_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_954_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_954_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
uint8_t v___x_937_; 
v___x_937_ = l_Lean_IR_IRType_isScalar(v_a_933_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_msg_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_msg_948_; lean_object* v___x_949_; 
lean_del_object(v___x_935_);
v___x_938_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_939_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_933_);
v___x_940_ = l_Std_Format_defWidth;
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = l_Std_Format_pretty(v___x_939_, v___x_940_, v___x_941_, v___x_941_);
v___x_943_ = lean_string_append(v___x_938_, v___x_942_);
lean_dec_ref(v___x_942_);
v___x_944_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_945_ = lean_string_append(v___x_943_, v___x_944_);
v___x_946_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_947_ = lean_string_append(v_msg_945_, v___x_946_);
v_msg_948_ = lean_string_append(v___x_947_, v___x_931_);
v___x_949_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_948_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_952_; 
lean_dec(v_a_933_);
v___x_950_ = lean_box(0);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_950_);
v___x_952_ = v___x_935_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_a_955_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_932_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_932_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_IR_Checker_checkScalarVar(v_x_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_974_, lean_object* v_ys_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_981_; 
lean_inc(v_c_974_);
v___x_981_ = l_Lean_IR_Checker_getDecl(v_c_974_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = lean_array_get_size(v_ys_975_);
v___x_984_ = l_Lean_IR_Decl_params(v_a_982_);
lean_dec(v_a_982_);
v___x_985_ = lean_array_get_size(v___x_984_);
lean_dec_ref(v___x_984_);
v___x_986_ = lean_nat_dec_eq(v___x_983_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_987_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_988_ = 1;
v___x_989_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_974_, v___x_988_);
v___x_990_ = lean_string_append(v___x_987_, v___x_989_);
lean_dec_ref(v___x_989_);
v___x_991_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
v___x_993_ = l_Nat_reprFast(v___x_983_);
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
lean_dec_ref(v___x_993_);
v___x_995_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_996_ = lean_string_append(v___x_994_, v___x_995_);
v___x_997_ = l_Nat_reprFast(v___x_985_);
v___x_998_ = lean_string_append(v___x_996_, v___x_997_);
lean_dec_ref(v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_1000_ = lean_string_append(v___x_998_, v___x_999_);
v___x_1001_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1000_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; 
lean_dec(v_c_974_);
v___x_1002_ = l_Lean_IR_Checker_checkArgs(v_ys_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_1002_;
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_c_974_);
v_a_1003_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_981_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_981_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_1011_, lean_object* v_ys_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_IR_Checker_checkFullApp(v_c_1011_, v_ys_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_ys_1012_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1022_, lean_object* v_ys_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; 
lean_inc(v_c_1022_);
v___x_1029_ = l_Lean_IR_Checker_getDecl(v_c_1022_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = lean_array_get_size(v_ys_1023_);
v___x_1032_ = l_Lean_IR_Decl_params(v_a_1030_);
lean_dec(v_a_1030_);
v___x_1033_ = lean_array_get_size(v___x_1032_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lean_nat_dec_lt(v___x_1031_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1035_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1036_ = 1;
v___x_1037_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1022_, v___x_1036_);
v___x_1038_ = lean_string_append(v___x_1035_, v___x_1037_);
lean_dec_ref(v___x_1037_);
v___x_1039_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1040_ = lean_string_append(v___x_1038_, v___x_1039_);
v___x_1041_ = l_Nat_reprFast(v___x_1031_);
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1044_ = lean_string_append(v___x_1042_, v___x_1043_);
v___x_1045_ = l_Nat_reprFast(v___x_1033_);
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1046_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; 
lean_dec(v_c_1022_);
v___x_1048_ = l_Lean_IR_Checker_checkArgs(v_ys_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1048_;
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_c_1022_);
v_a_1049_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1029_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1029_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1057_, lean_object* v_ys_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_IR_Checker_checkPartialApp(v_c_1057_, v_ys_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec_ref(v_ys_1058_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1072_, lean_object* v_e_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
switch(lean_obj_tag(v_e_1073_))
{
case 0:
{
lean_object* v_i_1079_; lean_object* v_ys_1080_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v_name_1091_; lean_object* v_cidx_1092_; lean_object* v_size_1093_; lean_object* v_usize_1094_; lean_object* v_ssize_1095_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_i_1079_ = lean_ctor_get(v_e_1073_, 0);
lean_inc_ref(v_i_1079_);
v_ys_1080_ = lean_ctor_get(v_e_1073_, 1);
lean_inc_ref(v_ys_1080_);
lean_dec_ref_known(v_e_1073_, 2);
v_name_1091_ = lean_ctor_get(v_i_1079_, 0);
v_cidx_1092_ = lean_ctor_get(v_i_1079_, 1);
v_size_1093_ = lean_ctor_get(v_i_1079_, 2);
v_usize_1094_ = lean_ctor_get(v_i_1079_, 3);
v_ssize_1095_ = lean_ctor_get(v_i_1079_, 4);
v___x_1125_ = l_Lean_maxCtorTag;
v___x_1126_ = lean_nat_dec_lt(v___x_1125_, v_cidx_1092_);
if (v___x_1126_ == 0)
{
v___y_1113_ = v_a_1074_;
v___y_1114_ = v_a_1075_;
v___y_1115_ = v_a_1076_;
v___y_1116_ = v_a_1077_;
goto v___jp_1112_;
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_IR_CtorInfo_isRef(v_i_1079_);
if (v___x_1127_ == 0)
{
v___y_1113_ = v_a_1074_;
v___y_1114_ = v_a_1075_;
v___y_1115_ = v_a_1076_;
v___y_1116_ = v_a_1077_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_inc(v_name_1091_);
lean_dec_ref(v_ys_1080_);
lean_dec_ref(v_i_1079_);
lean_dec(v_ty_1072_);
v___x_1128_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1129_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1091_, v___x_1127_);
v___x_1130_ = lean_string_append(v___x_1128_, v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1132_ = lean_string_append(v___x_1130_, v___x_1131_);
v___x_1133_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1132_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1133_;
}
}
v___jp_1081_:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Lean_IR_CtorInfo_isRef(v_i_1079_);
lean_dec_ref(v_i_1079_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec_ref(v_ys_1080_);
lean_dec(v_ty_1072_);
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v___x_1090_; 
lean_dec_ref_known(v___x_1089_, 1);
v___x_1090_ = l_Lean_IR_Checker_checkArgs(v_ys_1080_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec_ref(v_ys_1080_);
return v___x_1090_;
}
else
{
lean_dec_ref(v_ys_1080_);
return v___x_1089_;
}
}
}
v___jp_1096_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1101_ = l_Lean_maxCtorScalarsSize;
v___x_1102_ = l_Lean_usizeSize;
v___x_1103_ = lean_nat_mul(v_usize_1094_, v___x_1102_);
v___x_1104_ = lean_nat_add(v_ssize_1095_, v___x_1103_);
lean_dec(v___x_1103_);
v___x_1105_ = lean_nat_dec_lt(v___x_1101_, v___x_1104_);
lean_dec(v___x_1104_);
if (v___x_1105_ == 0)
{
v___y_1082_ = v___y_1097_;
v___y_1083_ = v___y_1098_;
v___y_1084_ = v___y_1099_;
v___y_1085_ = v___y_1100_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_inc(v_name_1091_);
lean_dec_ref(v_ys_1080_);
lean_dec_ref(v_i_1079_);
lean_dec(v_ty_1072_);
v___x_1106_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1107_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1091_, v___x_1105_);
v___x_1108_ = lean_string_append(v___x_1106_, v___x_1107_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1110_ = lean_string_append(v___x_1108_, v___x_1109_);
v___x_1111_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1110_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1111_;
}
}
v___jp_1112_:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = l_Lean_maxCtorNumObjs;
v___x_1118_ = lean_nat_dec_lt(v___x_1117_, v_size_1093_);
if (v___x_1118_ == 0)
{
v___y_1097_ = v___y_1113_;
v___y_1098_ = v___y_1114_;
v___y_1099_ = v___y_1115_;
v___y_1100_ = v___y_1116_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_inc(v_name_1091_);
lean_dec_ref(v_ys_1080_);
lean_dec_ref(v_i_1079_);
lean_dec(v_ty_1072_);
v___x_1119_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1120_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1091_, v___x_1118_);
v___x_1121_ = lean_string_append(v___x_1119_, v___x_1120_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1123_ = lean_string_append(v___x_1121_, v___x_1122_);
v___x_1124_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1123_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1124_;
}
}
}
case 1:
{
lean_object* v_x_1134_; lean_object* v___x_1135_; 
v_x_1134_ = lean_ctor_get(v_e_1073_, 1);
lean_inc(v_x_1134_);
lean_dec_ref_known(v_e_1073_, 2);
v___x_1135_ = l_Lean_IR_Checker_checkObjVar(v_x_1134_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; 
lean_dec_ref_known(v___x_1135_, 1);
v___x_1136_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1136_;
}
else
{
lean_dec(v_ty_1072_);
return v___x_1135_;
}
}
case 2:
{
lean_object* v_x_1137_; lean_object* v_ys_1138_; lean_object* v___x_1139_; 
v_x_1137_ = lean_ctor_get(v_e_1073_, 0);
lean_inc(v_x_1137_);
v_ys_1138_ = lean_ctor_get(v_e_1073_, 2);
lean_inc_ref(v_ys_1138_);
lean_dec_ref_known(v_e_1073_, 3);
v___x_1139_ = l_Lean_IR_Checker_checkObjVar(v_x_1137_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref_known(v___x_1139_, 1);
v___x_1140_ = l_Lean_IR_Checker_checkArgs(v_ys_1138_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec_ref(v_ys_1138_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref_known(v___x_1140_, 1);
v___x_1141_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1141_;
}
else
{
lean_dec(v_ty_1072_);
return v___x_1140_;
}
}
else
{
lean_dec_ref(v_ys_1138_);
lean_dec(v_ty_1072_);
return v___x_1139_;
}
}
case 3:
{
lean_object* v_i_1142_; lean_object* v_x_1143_; lean_object* v___x_1144_; 
v_i_1142_ = lean_ctor_get(v_e_1073_, 0);
lean_inc(v_i_1142_);
v_x_1143_ = lean_ctor_get(v_e_1073_, 1);
lean_inc(v_x_1143_);
lean_dec_ref_known(v_e_1073_, 2);
v___x_1144_ = l_Lean_IR_Checker_getType(v_x_1143_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1190_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1190_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1190_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
switch(lean_obj_tag(v_a_1145_))
{
case 7:
{
lean_object* v___x_1149_; 
lean_del_object(v___x_1147_);
lean_dec(v_i_1142_);
v___x_1149_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1149_;
}
case 8:
{
lean_object* v___x_1150_; 
lean_del_object(v___x_1147_);
lean_dec(v_i_1142_);
v___x_1150_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1150_;
}
case 10:
{
lean_object* v_types_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_types_1151_ = lean_ctor_get(v_a_1145_, 1);
lean_inc_ref(v_types_1151_);
lean_dec_ref_known(v_a_1145_, 2);
v___x_1152_ = lean_array_get_size(v_types_1151_);
v___x_1153_ = lean_nat_dec_lt(v_i_1142_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v_types_1151_);
lean_del_object(v___x_1147_);
lean_dec(v_i_1142_);
lean_dec(v_ty_1072_);
v___x_1154_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1155_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1154_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_array_fget(v_types_1151_, v_i_1142_);
lean_dec(v_i_1142_);
lean_dec_ref(v_types_1151_);
v___x_1157_ = l_Lean_IR_instBEqIRType_beq(v___x_1156_, v_ty_1072_);
lean_dec(v_ty_1072_);
lean_dec(v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_del_object(v___x_1147_);
v___x_1158_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1159_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1158_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = lean_box(0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1160_);
v___x_1162_ = v___x_1147_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
case 11:
{
lean_object* v_types_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v_types_1164_ = lean_ctor_get(v_a_1145_, 1);
lean_inc_ref(v_types_1164_);
lean_dec_ref_known(v_a_1145_, 2);
v___x_1165_ = lean_array_get_size(v_types_1164_);
v___x_1166_ = lean_nat_dec_lt(v_i_1142_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec_ref(v_types_1164_);
lean_del_object(v___x_1147_);
lean_dec(v_i_1142_);
lean_dec(v_ty_1072_);
v___x_1167_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1168_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1167_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_array_fget(v_types_1164_, v_i_1142_);
lean_dec(v_i_1142_);
lean_dec_ref(v_types_1164_);
v___x_1170_ = l_Lean_IR_instBEqIRType_beq(v___x_1169_, v_ty_1072_);
lean_dec(v_ty_1072_);
lean_dec(v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_del_object(v___x_1147_);
v___x_1171_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1172_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1171_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1173_);
v___x_1175_ = v___x_1147_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
case 12:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
lean_dec(v_i_1142_);
lean_dec(v_ty_1072_);
v___x_1177_ = lean_box(0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1177_);
v___x_1179_ = v___x_1147_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
default: 
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_del_object(v___x_1147_);
lean_dec(v_i_1142_);
lean_dec(v_ty_1072_);
v___x_1181_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1182_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1145_);
v___x_1183_ = l_Std_Format_defWidth;
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = l_Std_Format_pretty(v___x_1182_, v___x_1183_, v___x_1184_, v___x_1184_);
v___x_1186_ = lean_string_append(v___x_1181_, v___x_1185_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1188_ = lean_string_append(v___x_1186_, v___x_1187_);
v___x_1189_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1188_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_i_1142_);
lean_dec(v_ty_1072_);
v_a_1191_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1144_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1144_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
case 4:
{
lean_object* v_x_1199_; lean_object* v___x_1200_; 
v_x_1199_ = lean_ctor_get(v_e_1073_, 1);
lean_inc(v_x_1199_);
lean_dec_ref_known(v_e_1073_, 2);
v___x_1200_ = l_Lean_IR_Checker_checkObjVar(v_x_1199_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1219_; 
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; 
v_unused_1220_ = lean_ctor_get(v___x_1200_, 0);
lean_dec(v_unused_1220_);
v___x_1202_ = v___x_1200_;
v_isShared_1203_ = v_isSharedCheck_1219_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v___x_1200_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1219_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_box(5);
v___x_1205_ = l_Lean_IR_instBEqIRType_beq(v_ty_1072_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v_msg_1213_; lean_object* v___x_1214_; 
lean_del_object(v___x_1202_);
v___x_1206_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1207_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1072_);
v___x_1208_ = l_Std_Format_defWidth;
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = l_Std_Format_pretty(v___x_1207_, v___x_1208_, v___x_1209_, v___x_1209_);
v___x_1211_ = lean_string_append(v___x_1206_, v___x_1210_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1213_ = lean_string_append(v___x_1211_, v___x_1212_);
v___x_1214_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1213_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_dec(v_ty_1072_);
v___x_1215_ = lean_box(0);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1215_);
v___x_1217_ = v___x_1202_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_dec(v_ty_1072_);
return v___x_1200_;
}
}
case 5:
{
lean_object* v_x_1221_; lean_object* v___x_1222_; 
v_x_1221_ = lean_ctor_get(v_e_1073_, 2);
lean_inc(v_x_1221_);
lean_dec_ref_known(v_e_1073_, 3);
v___x_1222_ = l_Lean_IR_Checker_checkObjVar(v_x_1221_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1223_; 
lean_dec_ref_known(v___x_1222_, 1);
v___x_1223_ = l_Lean_IR_Checker_checkScalarType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1223_;
}
else
{
lean_dec(v_ty_1072_);
return v___x_1222_;
}
}
case 6:
{
lean_object* v_c_1224_; lean_object* v_ys_1225_; lean_object* v___x_1226_; 
lean_dec(v_ty_1072_);
v_c_1224_ = lean_ctor_get(v_e_1073_, 0);
lean_inc(v_c_1224_);
v_ys_1225_ = lean_ctor_get(v_e_1073_, 1);
lean_inc_ref(v_ys_1225_);
lean_dec_ref_known(v_e_1073_, 2);
v___x_1226_ = l_Lean_IR_Checker_checkFullApp(v_c_1224_, v_ys_1225_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec_ref(v_ys_1225_);
return v___x_1226_;
}
case 7:
{
lean_object* v_c_1227_; lean_object* v_ys_1228_; lean_object* v___x_1229_; 
v_c_1227_ = lean_ctor_get(v_e_1073_, 0);
lean_inc(v_c_1227_);
v_ys_1228_ = lean_ctor_get(v_e_1073_, 1);
lean_inc_ref(v_ys_1228_);
lean_dec_ref_known(v_e_1073_, 2);
v___x_1229_ = l_Lean_IR_Checker_checkPartialApp(v_c_1227_, v_ys_1228_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec_ref(v_ys_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref_known(v___x_1229_, 1);
v___x_1230_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1230_;
}
else
{
lean_dec(v_ty_1072_);
return v___x_1229_;
}
}
case 8:
{
lean_object* v_x_1231_; lean_object* v_ys_1232_; lean_object* v___x_1233_; 
v_x_1231_ = lean_ctor_get(v_e_1073_, 0);
lean_inc(v_x_1231_);
v_ys_1232_ = lean_ctor_get(v_e_1073_, 1);
lean_inc_ref(v_ys_1232_);
lean_dec_ref_known(v_e_1073_, 2);
v___x_1233_ = l_Lean_IR_Checker_checkObjVar(v_x_1231_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref_known(v___x_1233_, 1);
v___x_1234_ = l_Lean_IR_Checker_checkArgs(v_ys_1232_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec_ref(v_ys_1232_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref_known(v___x_1234_, 1);
v___x_1235_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1235_;
}
else
{
lean_dec(v_ty_1072_);
return v___x_1234_;
}
}
else
{
lean_dec_ref(v_ys_1232_);
lean_dec(v_ty_1072_);
return v___x_1233_;
}
}
case 9:
{
lean_object* v_ty_1236_; lean_object* v_x_1237_; lean_object* v___x_1238_; 
v_ty_1236_ = lean_ctor_get(v_e_1073_, 0);
lean_inc(v_ty_1236_);
v_x_1237_ = lean_ctor_get(v_e_1073_, 1);
lean_inc(v_x_1237_);
lean_dec_ref_known(v_e_1073_, 2);
v___x_1238_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref_known(v___x_1238_, 1);
lean_inc(v_x_1237_);
v___x_1239_ = l_Lean_IR_Checker_checkScalarVar(v_x_1237_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref_known(v___x_1239_, 1);
v___x_1240_ = l_Lean_IR_Checker_getType(v_x_1237_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1259_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1259_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1259_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
uint8_t v___x_1245_; 
v___x_1245_ = l_Lean_IR_instBEqIRType_beq(v_a_1241_, v_ty_1236_);
lean_dec(v_ty_1236_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_msg_1253_; lean_object* v___x_1254_; 
lean_del_object(v___x_1243_);
v___x_1246_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1247_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1241_);
v___x_1248_ = l_Std_Format_defWidth;
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = l_Std_Format_pretty(v___x_1247_, v___x_1248_, v___x_1249_, v___x_1249_);
v___x_1251_ = lean_string_append(v___x_1246_, v___x_1250_);
lean_dec_ref(v___x_1250_);
v___x_1252_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1253_ = lean_string_append(v___x_1251_, v___x_1252_);
v___x_1254_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1253_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
lean_dec(v_a_1241_);
v___x_1255_ = lean_box(0);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1255_);
v___x_1257_ = v___x_1243_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_ty_1236_);
v_a_1260_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1240_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1240_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_dec(v_x_1237_);
lean_dec(v_ty_1236_);
return v___x_1239_;
}
}
else
{
lean_dec(v_x_1237_);
lean_dec(v_ty_1236_);
return v___x_1238_;
}
}
case 10:
{
lean_object* v_x_1268_; lean_object* v___x_1269_; 
v_x_1268_ = lean_ctor_get(v_e_1073_, 0);
lean_inc(v_x_1268_);
lean_dec_ref_known(v_e_1073_, 1);
v___x_1269_ = l_Lean_IR_Checker_checkScalarType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v___x_1270_; 
lean_dec_ref_known(v___x_1269_, 1);
v___x_1270_ = l_Lean_IR_Checker_checkObjVar(v_x_1268_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1270_;
}
else
{
lean_dec(v_x_1268_);
return v___x_1269_;
}
}
case 11:
{
lean_object* v_v_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1280_; 
v_v_1271_ = lean_ctor_get(v_e_1073_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_e_1073_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1273_ = v_e_1073_;
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_v_1271_);
lean_dec(v_e_1073_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
if (lean_obj_tag(v_v_1271_) == 1)
{
lean_object* v___x_1275_; 
lean_dec_ref_known(v_v_1271_, 1);
lean_del_object(v___x_1273_);
v___x_1275_ = l_Lean_IR_Checker_checkObjType(v_ty_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
lean_dec_ref(v_v_1271_);
lean_dec(v_ty_1072_);
v___x_1276_ = lean_box(0);
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
default: 
{
lean_object* v_x_1281_; lean_object* v___x_1282_; 
v_x_1281_ = lean_ctor_get(v_e_1073_, 0);
lean_inc(v_x_1281_);
lean_dec_ref_known(v_e_1073_, 1);
v___x_1282_ = l_Lean_IR_Checker_checkObjVar(v_x_1281_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1301_; 
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v___x_1282_, 0);
lean_dec(v_unused_1302_);
v___x_1284_ = v___x_1282_;
v_isShared_1285_ = v_isSharedCheck_1301_;
goto v_resetjp_1283_;
}
else
{
lean_dec(v___x_1282_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1301_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = lean_box(1);
v___x_1287_ = l_Lean_IR_instBEqIRType_beq(v_ty_1072_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_msg_1295_; lean_object* v___x_1296_; 
lean_del_object(v___x_1284_);
v___x_1288_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1289_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1072_);
v___x_1290_ = l_Std_Format_defWidth;
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = l_Std_Format_pretty(v___x_1289_, v___x_1290_, v___x_1291_, v___x_1291_);
v___x_1293_ = lean_string_append(v___x_1288_, v___x_1292_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1295_ = lean_string_append(v___x_1293_, v___x_1294_);
v___x_1296_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1295_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_dec(v_ty_1072_);
v___x_1297_ = lean_box(0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1297_);
v___x_1299_ = v___x_1284_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_dec(v_ty_1072_);
return v___x_1282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1303_, lean_object* v_e_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_IR_Checker_checkExpr(v_ty_1303_, v_e_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1311_, lean_object* v_p_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_x_1318_; lean_object* v___x_1319_; 
v_x_1318_ = lean_ctor_get(v_p_1312_, 0);
lean_inc(v_x_1318_);
v___x_1319_ = l_Lean_IR_Checker_markVar(v_x_1318_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v___x_1319_, 0);
lean_dec(v_unused_1328_);
v___x_1321_ = v___x_1319_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v___x_1319_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = l_Lean_IR_LocalContext_addParam(v_ctx_1311_, v_p_1312_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_p_1312_);
lean_dec_ref(v_ctx_1311_);
v_a_1329_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1319_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1319_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1337_, lean_object* v_p_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1337_, v_p_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1344_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_instMonadEIO___redArg();
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1347_ = l_StateRefT_x27_instMonad___redArg(v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1351_, lean_object* v_k_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v___x_1358_; lean_object* v_toApplicative_1359_; lean_object* v_toFunctor_1360_; lean_object* v_toSeq_1361_; lean_object* v_toSeqLeft_1362_; lean_object* v_toSeqRight_1363_; lean_object* v___f_1364_; lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___f_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_localCtx_1376_; lean_object* v_currentDecl_1377_; lean_object* v_decls_1378_; lean_object* v_a_1380_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1358_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1359_ = lean_ctor_get(v___x_1358_, 0);
v_toFunctor_1360_ = lean_ctor_get(v_toApplicative_1359_, 0);
v_toSeq_1361_ = lean_ctor_get(v_toApplicative_1359_, 2);
v_toSeqLeft_1362_ = lean_ctor_get(v_toApplicative_1359_, 3);
v_toSeqRight_1363_ = lean_ctor_get(v_toApplicative_1359_, 4);
v___f_1364_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1365_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1360_, 2);
v___f_1366_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1366_, 0, v_toFunctor_1360_);
v___f_1367_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1367_, 0, v_toFunctor_1360_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___f_1366_);
lean_ctor_set(v___x_1368_, 1, v___f_1367_);
lean_inc(v_toSeqRight_1363_);
v___f_1369_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1369_, 0, v_toSeqRight_1363_);
lean_inc(v_toSeqLeft_1362_);
v___f_1370_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1370_, 0, v_toSeqLeft_1362_);
lean_inc(v_toSeq_1361_);
v___f_1371_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1371_, 0, v_toSeq_1361_);
v___x_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1368_);
lean_ctor_set(v___x_1372_, 1, v___f_1364_);
lean_ctor_set(v___x_1372_, 2, v___f_1371_);
lean_ctor_set(v___x_1372_, 3, v___f_1370_);
lean_ctor_set(v___x_1372_, 4, v___f_1369_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___f_1365_);
v___x_1374_ = l_StateRefT_x27_instMonad___redArg(v___x_1373_);
v___x_1375_ = l_ReaderT_instMonad___redArg(v___x_1374_);
v_localCtx_1376_ = lean_ctor_get(v_a_1353_, 0);
v_currentDecl_1377_ = lean_ctor_get(v_a_1353_, 1);
v_decls_1378_ = lean_ctor_get(v_a_1353_, 2);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_array_get_size(v_ps_1351_);
v___x_1385_ = lean_nat_dec_lt(v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_ps_1351_);
lean_inc_ref(v_localCtx_1376_);
v_a_1380_ = v_localCtx_1376_;
goto v___jp_1379_;
}
else
{
lean_object* v___f_1386_; size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1038__overap_1389_; lean_object* v___x_1390_; 
v___f_1386_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = lean_usize_of_nat(v___x_1384_);
lean_inc_ref(v_localCtx_1376_);
v___x_1038__overap_1389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1375_, v___f_1386_, v_ps_1351_, v___x_1387_, v___x_1388_, v_localCtx_1376_);
lean_inc(v_a_1356_);
lean_inc_ref(v_a_1355_);
lean_inc(v_a_1354_);
lean_inc_ref(v_a_1353_);
v___x_1390_ = lean_apply_5(v___x_1038__overap_1389_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, lean_box(0));
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v_a_1380_ = v_a_1391_;
goto v___jp_1379_;
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v_k_1352_);
v_a_1392_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1390_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1390_);
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
v___jp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_inc_ref(v_decls_1378_);
lean_inc_ref(v_currentDecl_1377_);
v___x_1381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1381_, 0, v_a_1380_);
lean_ctor_set(v___x_1381_, 1, v_currentDecl_1377_);
lean_ctor_set(v___x_1381_, 2, v_decls_1378_);
lean_inc(v_a_1356_);
lean_inc_ref(v_a_1355_);
lean_inc(v_a_1354_);
v___x_1382_ = lean_apply_5(v_k_1352_, v___x_1381_, v_a_1354_, v_a_1355_, v_a_1356_, lean_box(0));
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1400_, lean_object* v_k_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_IR_Checker_withParams(v_ps_1400_, v_k_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1408_, size_t v_i_1409_, size_t v_stop_1410_, lean_object* v_b_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_eq(v_i_1409_, v_stop_1410_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v_x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_array_uget_borrowed(v_as_1408_, v_i_1409_);
v_x_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_x_1419_);
v___x_1420_ = l_Lean_IR_Checker_markVar(v_x_1419_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; size_t v___x_1422_; size_t v___x_1423_; 
lean_dec_ref_known(v___x_1420_, 1);
lean_inc(v___x_1418_);
v___x_1421_ = l_Lean_IR_LocalContext_addParam(v_b_1411_, v___x_1418_);
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_add(v_i_1409_, v___x_1422_);
v_i_1409_ = v___x_1423_;
v_b_1411_ = v___x_1421_;
goto _start;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_b_1411_);
v_a_1425_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1420_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1420_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_b_1411_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1434_, lean_object* v_i_1435_, lean_object* v_stop_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
size_t v_i_boxed_1443_; size_t v_stop_boxed_1444_; lean_object* v_res_1445_; 
v_i_boxed_1443_ = lean_unbox_usize(v_i_1435_);
lean_dec(v_i_1435_);
v_stop_boxed_1444_ = lean_unbox_usize(v_stop_1436_);
lean_dec(v_stop_1436_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1434_, v_i_boxed_1443_, v_stop_boxed_1444_, v_b_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec_ref(v_as_1434_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_x_1453_; lean_object* v_b_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; 
switch(lean_obj_tag(v_fnBody_1446_))
{
case 0:
{
lean_object* v_x_1461_; lean_object* v_ty_1462_; lean_object* v_e_1463_; lean_object* v_b_1464_; lean_object* v___x_1465_; 
v_x_1461_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_x_1461_);
v_ty_1462_ = lean_ctor_get(v_fnBody_1446_, 1);
lean_inc_n(v_ty_1462_, 2);
v_e_1463_ = lean_ctor_get(v_fnBody_1446_, 2);
lean_inc_ref_n(v_e_1463_, 2);
v_b_1464_ = lean_ctor_get(v_fnBody_1446_, 3);
lean_inc(v_b_1464_);
lean_dec_ref_known(v_fnBody_1446_, 4);
v___x_1465_ = l_Lean_IR_Checker_checkExpr(v_ty_1462_, v_e_1463_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; 
lean_dec_ref_known(v___x_1465_, 1);
lean_inc(v_x_1461_);
v___x_1466_ = l_Lean_IR_Checker_markVar(v_x_1461_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_localCtx_1467_; lean_object* v_currentDecl_1468_; lean_object* v_decls_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref_known(v___x_1466_, 1);
v_localCtx_1467_ = lean_ctor_get(v_a_1447_, 0);
lean_inc_ref(v_localCtx_1467_);
v_currentDecl_1468_ = lean_ctor_get(v_a_1447_, 1);
lean_inc_ref(v_currentDecl_1468_);
v_decls_1469_ = lean_ctor_get(v_a_1447_, 2);
lean_inc_ref(v_decls_1469_);
lean_dec_ref(v_a_1447_);
v___x_1470_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1467_, v_x_1461_, v_ty_1462_, v_e_1463_);
v___x_1471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v_currentDecl_1468_);
lean_ctor_set(v___x_1471_, 2, v_decls_1469_);
v_fnBody_1446_ = v_b_1464_;
v_a_1447_ = v___x_1471_;
goto _start;
}
else
{
lean_dec(v_b_1464_);
lean_dec_ref(v_e_1463_);
lean_dec(v_ty_1462_);
lean_dec(v_x_1461_);
lean_dec_ref(v_a_1447_);
return v___x_1466_;
}
}
else
{
lean_dec(v_b_1464_);
lean_dec_ref(v_e_1463_);
lean_dec(v_ty_1462_);
lean_dec(v_x_1461_);
lean_dec_ref(v_a_1447_);
return v___x_1465_;
}
}
case 1:
{
lean_object* v_j_1473_; lean_object* v_xs_1474_; lean_object* v_v_1475_; lean_object* v_b_1476_; lean_object* v_a_1478_; lean_object* v___x_1487_; 
v_j_1473_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc_n(v_j_1473_, 2);
v_xs_1474_ = lean_ctor_get(v_fnBody_1446_, 1);
lean_inc_ref(v_xs_1474_);
v_v_1475_ = lean_ctor_get(v_fnBody_1446_, 2);
lean_inc(v_v_1475_);
v_b_1476_ = lean_ctor_get(v_fnBody_1446_, 3);
lean_inc(v_b_1476_);
lean_dec_ref_known(v_fnBody_1446_, 4);
v___x_1487_ = l_Lean_IR_Checker_markJP(v_j_1473_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_localCtx_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
lean_dec_ref_known(v___x_1487_, 1);
v_localCtx_1488_ = lean_ctor_get(v_a_1447_, 0);
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_array_get_size(v_xs_1474_);
v___x_1491_ = lean_nat_dec_lt(v___x_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_inc_ref(v_localCtx_1488_);
v_a_1478_ = v_localCtx_1488_;
goto v___jp_1477_;
}
else
{
size_t v___x_1492_; size_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = ((size_t)0ULL);
v___x_1493_ = lean_usize_of_nat(v___x_1490_);
lean_inc_ref(v_localCtx_1488_);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1474_, v___x_1492_, v___x_1493_, v_localCtx_1488_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v_a_1478_ = v_a_1495_;
goto v___jp_1477_;
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_b_1476_);
lean_dec(v_v_1475_);
lean_dec_ref(v_xs_1474_);
lean_dec(v_j_1473_);
lean_dec_ref(v_a_1447_);
v_a_1496_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1494_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1494_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
else
{
lean_dec(v_b_1476_);
lean_dec(v_v_1475_);
lean_dec_ref(v_xs_1474_);
lean_dec(v_j_1473_);
lean_dec_ref(v_a_1447_);
return v___x_1487_;
}
v___jp_1477_:
{
lean_object* v_localCtx_1479_; lean_object* v_currentDecl_1480_; lean_object* v_decls_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_localCtx_1479_ = lean_ctor_get(v_a_1447_, 0);
lean_inc_ref(v_localCtx_1479_);
v_currentDecl_1480_ = lean_ctor_get(v_a_1447_, 1);
lean_inc_ref_n(v_currentDecl_1480_, 2);
v_decls_1481_ = lean_ctor_get(v_a_1447_, 2);
lean_inc_ref_n(v_decls_1481_, 2);
lean_dec_ref(v_a_1447_);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v_a_1478_);
lean_ctor_set(v___x_1482_, 1, v_currentDecl_1480_);
lean_ctor_set(v___x_1482_, 2, v_decls_1481_);
lean_inc(v_v_1475_);
v___x_1483_ = l_Lean_IR_Checker_checkFnBody(v_v_1475_, v___x_1482_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref_known(v___x_1483_, 1);
v___x_1484_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1479_, v_j_1473_, v_xs_1474_, v_v_1475_);
v___x_1485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v_currentDecl_1480_);
lean_ctor_set(v___x_1485_, 2, v_decls_1481_);
v_fnBody_1446_ = v_b_1476_;
v_a_1447_ = v___x_1485_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1481_);
lean_dec_ref(v_currentDecl_1480_);
lean_dec_ref(v_localCtx_1479_);
lean_dec(v_b_1476_);
lean_dec(v_v_1475_);
lean_dec_ref(v_xs_1474_);
lean_dec(v_j_1473_);
return v___x_1483_;
}
}
}
case 2:
{
lean_object* v_x_1504_; lean_object* v_y_1505_; lean_object* v_b_1506_; lean_object* v___x_1507_; 
v_x_1504_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_x_1504_);
v_y_1505_ = lean_ctor_get(v_fnBody_1446_, 2);
lean_inc(v_y_1505_);
v_b_1506_ = lean_ctor_get(v_fnBody_1446_, 3);
lean_inc(v_b_1506_);
lean_dec_ref_known(v_fnBody_1446_, 4);
v___x_1507_ = l_Lean_IR_Checker_checkVar(v_x_1504_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; 
lean_dec_ref_known(v___x_1507_, 1);
v___x_1508_ = l_Lean_IR_Checker_checkArg(v_y_1505_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_dec_ref_known(v___x_1508_, 1);
v_fnBody_1446_ = v_b_1506_;
goto _start;
}
else
{
lean_dec(v_b_1506_);
lean_dec_ref(v_a_1447_);
return v___x_1508_;
}
}
else
{
lean_dec(v_b_1506_);
lean_dec(v_y_1505_);
lean_dec_ref(v_a_1447_);
return v___x_1507_;
}
}
case 3:
{
lean_object* v_x_1510_; lean_object* v_b_1511_; lean_object* v___x_1512_; 
v_x_1510_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_x_1510_);
v_b_1511_ = lean_ctor_get(v_fnBody_1446_, 2);
lean_inc(v_b_1511_);
lean_dec_ref_known(v_fnBody_1446_, 3);
v___x_1512_ = l_Lean_IR_Checker_checkVar(v_x_1510_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_dec_ref_known(v___x_1512_, 1);
v_fnBody_1446_ = v_b_1511_;
goto _start;
}
else
{
lean_dec(v_b_1511_);
lean_dec_ref(v_a_1447_);
return v___x_1512_;
}
}
case 4:
{
lean_object* v_x_1514_; lean_object* v_y_1515_; lean_object* v_b_1516_; lean_object* v___x_1517_; 
v_x_1514_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_x_1514_);
v_y_1515_ = lean_ctor_get(v_fnBody_1446_, 2);
lean_inc(v_y_1515_);
v_b_1516_ = lean_ctor_get(v_fnBody_1446_, 3);
lean_inc(v_b_1516_);
lean_dec_ref_known(v_fnBody_1446_, 4);
v___x_1517_ = l_Lean_IR_Checker_checkVar(v_x_1514_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v___x_1518_; 
lean_dec_ref_known(v___x_1517_, 1);
v___x_1518_ = l_Lean_IR_Checker_checkVar(v_y_1515_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_dec_ref_known(v___x_1518_, 1);
v_fnBody_1446_ = v_b_1516_;
goto _start;
}
else
{
lean_dec(v_b_1516_);
lean_dec_ref(v_a_1447_);
return v___x_1518_;
}
}
else
{
lean_dec(v_b_1516_);
lean_dec(v_y_1515_);
lean_dec_ref(v_a_1447_);
return v___x_1517_;
}
}
case 5:
{
lean_object* v_x_1520_; lean_object* v_y_1521_; lean_object* v_b_1522_; lean_object* v___x_1523_; 
v_x_1520_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_x_1520_);
v_y_1521_ = lean_ctor_get(v_fnBody_1446_, 3);
lean_inc(v_y_1521_);
v_b_1522_ = lean_ctor_get(v_fnBody_1446_, 5);
lean_inc(v_b_1522_);
lean_dec_ref_known(v_fnBody_1446_, 6);
v___x_1523_ = l_Lean_IR_Checker_checkVar(v_x_1520_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1524_; 
lean_dec_ref_known(v___x_1523_, 1);
v___x_1524_ = l_Lean_IR_Checker_checkVar(v_y_1521_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_dec_ref_known(v___x_1524_, 1);
v_fnBody_1446_ = v_b_1522_;
goto _start;
}
else
{
lean_dec(v_b_1522_);
lean_dec_ref(v_a_1447_);
return v___x_1524_;
}
}
else
{
lean_dec(v_b_1522_);
lean_dec(v_y_1521_);
lean_dec_ref(v_a_1447_);
return v___x_1523_;
}
}
case 8:
{
lean_object* v_x_1526_; lean_object* v_b_1527_; lean_object* v___x_1528_; 
v_x_1526_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_x_1526_);
v_b_1527_ = lean_ctor_get(v_fnBody_1446_, 1);
lean_inc(v_b_1527_);
lean_dec_ref_known(v_fnBody_1446_, 2);
v___x_1528_ = l_Lean_IR_Checker_checkVar(v_x_1526_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_dec_ref_known(v___x_1528_, 1);
v_fnBody_1446_ = v_b_1527_;
goto _start;
}
else
{
lean_dec(v_b_1527_);
lean_dec_ref(v_a_1447_);
return v___x_1528_;
}
}
case 9:
{
lean_object* v_x_1530_; lean_object* v_cs_1531_; lean_object* v___x_1532_; 
v_x_1530_ = lean_ctor_get(v_fnBody_1446_, 1);
lean_inc(v_x_1530_);
v_cs_1531_ = lean_ctor_get(v_fnBody_1446_, 3);
lean_inc_ref(v_cs_1531_);
lean_dec_ref_known(v_fnBody_1446_, 4);
v___x_1532_ = l_Lean_IR_Checker_checkVar(v_x_1530_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1546_; 
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1532_, 0);
lean_dec(v_unused_1547_);
v___x_1534_ = v___x_1532_;
v_isShared_1535_ = v_isSharedCheck_1546_;
goto v_resetjp_1533_;
}
else
{
lean_dec(v___x_1532_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1546_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_array_get_size(v_cs_1531_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_nat_dec_lt(v___x_1536_, v___x_1537_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref(v_cs_1531_);
lean_dec_ref(v_a_1447_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1538_);
v___x_1541_ = v___x_1534_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1538_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
else
{
size_t v___x_1543_; size_t v___x_1544_; lean_object* v___x_1545_; 
lean_del_object(v___x_1534_);
v___x_1543_ = ((size_t)0ULL);
v___x_1544_ = lean_usize_of_nat(v___x_1537_);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1531_, v___x_1543_, v___x_1544_, v___x_1538_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
lean_dec_ref(v_a_1447_);
lean_dec_ref(v_cs_1531_);
return v___x_1545_;
}
}
}
else
{
lean_dec_ref(v_cs_1531_);
lean_dec_ref(v_a_1447_);
return v___x_1532_;
}
}
case 10:
{
lean_object* v_x_1548_; lean_object* v___x_1549_; 
v_x_1548_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_x_1548_);
lean_dec_ref_known(v_fnBody_1446_, 1);
v___x_1549_ = l_Lean_IR_Checker_checkArg(v_x_1548_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
lean_dec_ref(v_a_1447_);
return v___x_1549_;
}
case 11:
{
lean_object* v_j_1550_; lean_object* v_ys_1551_; lean_object* v___x_1552_; 
v_j_1550_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_j_1550_);
v_ys_1551_ = lean_ctor_get(v_fnBody_1446_, 1);
lean_inc_ref(v_ys_1551_);
lean_dec_ref_known(v_fnBody_1446_, 2);
v___x_1552_ = l_Lean_IR_Checker_checkJP(v_j_1550_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref_known(v___x_1552_, 1);
v___x_1553_ = l_Lean_IR_Checker_checkArgs(v_ys_1551_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
lean_dec_ref(v_a_1447_);
lean_dec_ref(v_ys_1551_);
return v___x_1553_;
}
else
{
lean_dec_ref(v_ys_1551_);
lean_dec_ref(v_a_1447_);
return v___x_1552_;
}
}
case 12:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec_ref(v_a_1447_);
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
default: 
{
lean_object* v_x_1556_; lean_object* v_b_1557_; 
v_x_1556_ = lean_ctor_get(v_fnBody_1446_, 0);
lean_inc(v_x_1556_);
v_b_1557_ = lean_ctor_get(v_fnBody_1446_, 2);
lean_inc(v_b_1557_);
lean_dec(v_fnBody_1446_);
v_x_1453_ = v_x_1556_;
v_b_1454_ = v_b_1557_;
v___y_1455_ = v_a_1447_;
v___y_1456_ = v_a_1448_;
v___y_1457_ = v_a_1449_;
v___y_1458_ = v_a_1450_;
goto v___jp_1452_;
}
}
v___jp_1452_:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_IR_Checker_checkVar(v_x_1453_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_dec_ref_known(v___x_1459_, 1);
v_fnBody_1446_ = v_b_1454_;
v_a_1447_ = v___y_1455_;
v_a_1448_ = v___y_1456_;
v_a_1449_ = v___y_1457_;
v_a_1450_ = v___y_1458_;
goto _start;
}
else
{
lean_dec_ref(v___y_1455_);
lean_dec(v_b_1454_);
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1558_, size_t v_i_1559_, size_t v_stop_1560_, lean_object* v_b_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_usize_dec_eq(v_i_1559_, v_stop_1560_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_array_uget_borrowed(v_as_1558_, v_i_1559_);
v___x_1569_ = l_Lean_IR_Alt_body(v___x_1568_);
lean_inc_ref(v___y_1562_);
v___x_1570_ = l_Lean_IR_Checker_checkFnBody(v___x_1569_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; size_t v___x_1572_; size_t v___x_1573_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = ((size_t)1ULL);
v___x_1573_ = lean_usize_add(v_i_1559_, v___x_1572_);
v_i_1559_ = v___x_1573_;
v_b_1561_ = v_a_1571_;
goto _start;
}
else
{
return v___x_1570_;
}
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_b_1561_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1576_, lean_object* v_i_1577_, lean_object* v_stop_1578_, lean_object* v_b_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
size_t v_i_boxed_1585_; size_t v_stop_boxed_1586_; lean_object* v_res_1587_; 
v_i_boxed_1585_ = lean_unbox_usize(v_i_1577_);
lean_dec(v_i_1577_);
v_stop_boxed_1586_ = lean_unbox_usize(v_stop_1578_);
lean_dec(v_stop_1578_);
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1576_, v_i_boxed_1585_, v_stop_boxed_1586_, v_b_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v_as_1576_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
if (lean_obj_tag(v_x_1595_) == 0)
{
lean_object* v_xs_1601_; lean_object* v_body_1602_; lean_object* v_localCtx_1603_; lean_object* v_currentDecl_1604_; lean_object* v_decls_1605_; lean_object* v_a_1607_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v_xs_1601_ = lean_ctor_get(v_x_1595_, 1);
lean_inc_ref(v_xs_1601_);
v_body_1602_ = lean_ctor_get(v_x_1595_, 3);
lean_inc(v_body_1602_);
lean_dec_ref_known(v_x_1595_, 5);
v_localCtx_1603_ = lean_ctor_get(v_a_1596_, 0);
v_currentDecl_1604_ = lean_ctor_get(v_a_1596_, 1);
v_decls_1605_ = lean_ctor_get(v_a_1596_, 2);
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = lean_array_get_size(v_xs_1601_);
v___x_1612_ = lean_nat_dec_lt(v___x_1610_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_dec_ref(v_xs_1601_);
lean_inc_ref(v_localCtx_1603_);
v_a_1607_ = v_localCtx_1603_;
goto v___jp_1606_;
}
else
{
size_t v___x_1613_; size_t v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = ((size_t)0ULL);
v___x_1614_ = lean_usize_of_nat(v___x_1611_);
lean_inc_ref(v_localCtx_1603_);
v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1601_, v___x_1613_, v___x_1614_, v_localCtx_1603_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
lean_dec_ref(v_xs_1601_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v_a_1607_ = v_a_1616_;
goto v___jp_1606_;
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_body_1602_);
v_a_1617_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1615_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1615_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
v___jp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_inc_ref(v_decls_1605_);
lean_inc_ref(v_currentDecl_1604_);
v___x_1608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1608_, 0, v_a_1607_);
lean_ctor_set(v___x_1608_, 1, v_currentDecl_1604_);
lean_ctor_set(v___x_1608_, 2, v_decls_1605_);
v___x_1609_ = l_Lean_IR_Checker_checkFnBody(v_body_1602_, v___x_1608_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1609_;
}
}
else
{
lean_object* v_xs_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v_xs_1625_ = lean_ctor_get(v_x_1595_, 1);
lean_inc_ref(v_xs_1625_);
lean_dec_ref_known(v_x_1595_, 4);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_array_get_size(v_xs_1625_);
v___x_1629_ = lean_nat_dec_lt(v___x_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_dec_ref(v_xs_1625_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1626_);
return v___x_1630_;
}
else
{
lean_object* v_localCtx_1631_; size_t v___x_1632_; size_t v___x_1633_; lean_object* v___x_1634_; 
v_localCtx_1631_ = lean_ctor_get(v_a_1596_, 0);
v___x_1632_ = ((size_t)0ULL);
v___x_1633_ = lean_usize_of_nat(v___x_1628_);
lean_inc_ref(v_localCtx_1631_);
v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1625_, v___x_1632_, v___x_1633_, v_localCtx_1631_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
lean_dec_ref(v_xs_1625_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v___x_1634_, 0);
lean_dec(v_unused_1642_);
v___x_1636_ = v___x_1634_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_dec(v___x_1634_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1626_);
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1626_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1634_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1634_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_IR_Checker_checkDecl(v_x_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_1662_, lean_object* v_decl_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1667_ = ((lean_object*)(l_Lean_IR_checkDecl___closed__0));
lean_inc_ref(v_decl_1663_);
v___x_1668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v_decl_1663_);
lean_ctor_set(v___x_1668_, 2, v_decls_1662_);
v___x_1669_ = ((lean_object*)(l_Lean_IR_checkDecl___closed__1));
v___x_1670_ = lean_st_mk_ref(v___x_1669_);
v___x_1671_ = l_Lean_IR_Checker_checkDecl(v_decl_1663_, v___x_1668_, v___x_1670_, v_a_1664_, v_a_1665_);
lean_dec_ref_known(v___x_1668_, 3);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1680_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_st_ref_get(v___x_1670_);
lean_dec(v___x_1670_);
lean_dec(v___x_1676_);
if (v_isShared_1675_ == 0)
{
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1672_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_dec(v___x_1670_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* v_decls_1681_, lean_object* v_decl_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_IR_checkDecl(v_decls_1681_, v_decl_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* v_decls_1687_, lean_object* v_as_1688_, size_t v_i_1689_, size_t v_stop_1690_, lean_object* v_b_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_usize_dec_eq(v_i_1689_, v_stop_1690_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_array_uget_borrowed(v_as_1688_, v_i_1689_);
lean_inc(v___x_1696_);
lean_inc_ref(v_decls_1687_);
v___x_1697_ = l_Lean_IR_checkDecl(v_decls_1687_, v___x_1696_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; size_t v___x_1699_; size_t v___x_1700_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = lean_usize_add(v_i_1689_, v___x_1699_);
v_i_1689_ = v___x_1700_;
v_b_1691_ = v_a_1698_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1687_);
return v___x_1697_;
}
}
else
{
lean_object* v___x_1702_; 
lean_dec_ref(v_decls_1687_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_b_1691_);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* v_decls_1703_, lean_object* v_as_1704_, lean_object* v_i_1705_, lean_object* v_stop_1706_, lean_object* v_b_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
size_t v_i_boxed_1711_; size_t v_stop_boxed_1712_; lean_object* v_res_1713_; 
v_i_boxed_1711_ = lean_unbox_usize(v_i_1705_);
lean_dec(v_i_1705_);
v_stop_boxed_1712_ = lean_unbox_usize(v_stop_1706_);
lean_dec(v_stop_1706_);
v_res_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1703_, v_as_1704_, v_i_boxed_1711_, v_stop_boxed_1712_, v_b_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec_ref(v_as_1704_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* v_decls_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1718_ = lean_unsigned_to_nat(0u);
v___x_1719_ = lean_array_get_size(v_decls_1714_);
v___x_1720_ = lean_box(0);
v___x_1721_ = lean_nat_dec_lt(v___x_1718_, v___x_1719_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec_ref(v_decls_1714_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
return v___x_1722_;
}
else
{
size_t v___x_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = lean_usize_of_nat(v___x_1719_);
lean_inc_ref(v_decls_1714_);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1714_, v_decls_1714_, v___x_1723_, v___x_1724_, v___x_1720_, v_a_1715_, v_a_1716_);
lean_dec_ref(v_decls_1714_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_IR_checkDecls(v_decls_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1730_;
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
