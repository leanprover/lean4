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
extern lean_object* l_Lean_usizeSize;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxCtorScalarsSize;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_maxCtorFields;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_markIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "variable / join point index "};
static const lean_object* l_Lean_IR_Checker_markIndex___closed__0 = (const lean_object*)&l_Lean_IR_Checker_markIndex___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_markIndex___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " has already been used"};
static const lean_object* l_Lean_IR_Checker_markIndex___closed__1 = (const lean_object*)&l_Lean_IR_Checker_markIndex___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' has too many fields"};
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object* v_k_123_, lean_object* v_v_124_, lean_object* v_t_125_){
_start:
{
if (lean_obj_tag(v_t_125_) == 0)
{
lean_object* v_size_126_; lean_object* v_k_127_; lean_object* v_v_128_; lean_object* v_l_129_; lean_object* v_r_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_411_; 
v_size_126_ = lean_ctor_get(v_t_125_, 0);
v_k_127_ = lean_ctor_get(v_t_125_, 1);
v_v_128_ = lean_ctor_get(v_t_125_, 2);
v_l_129_ = lean_ctor_get(v_t_125_, 3);
v_r_130_ = lean_ctor_get(v_t_125_, 4);
v_isSharedCheck_411_ = !lean_is_exclusive(v_t_125_);
if (v_isSharedCheck_411_ == 0)
{
v___x_132_ = v_t_125_;
v_isShared_133_ = v_isSharedCheck_411_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_r_130_);
lean_inc(v_l_129_);
lean_inc(v_v_128_);
lean_inc(v_k_127_);
lean_inc(v_size_126_);
lean_dec(v_t_125_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_411_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_lt(v_k_123_, v_k_127_);
if (v___x_134_ == 0)
{
uint8_t v___x_135_; 
v___x_135_ = lean_nat_dec_eq(v_k_123_, v_k_127_);
if (v___x_135_ == 0)
{
lean_object* v_impl_136_; lean_object* v___x_137_; 
lean_dec(v_size_126_);
v_impl_136_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_123_, v_v_124_, v_r_130_);
v___x_137_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_129_) == 0)
{
lean_object* v_size_138_; lean_object* v_size_139_; lean_object* v_k_140_; lean_object* v_v_141_; lean_object* v_l_142_; lean_object* v_r_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_size_138_ = lean_ctor_get(v_l_129_, 0);
v_size_139_ = lean_ctor_get(v_impl_136_, 0);
v_k_140_ = lean_ctor_get(v_impl_136_, 1);
v_v_141_ = lean_ctor_get(v_impl_136_, 2);
v_l_142_ = lean_ctor_get(v_impl_136_, 3);
lean_inc(v_l_142_);
v_r_143_ = lean_ctor_get(v_impl_136_, 4);
v___x_144_ = lean_unsigned_to_nat(3u);
v___x_145_ = lean_nat_mul(v___x_144_, v_size_138_);
v___x_146_ = lean_nat_dec_lt(v___x_145_, v_size_139_);
lean_dec(v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
lean_dec(v_l_142_);
v___x_147_ = lean_nat_add(v___x_137_, v_size_138_);
v___x_148_ = lean_nat_add(v___x_147_, v_size_139_);
lean_dec(v___x_147_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_impl_136_);
lean_ctor_set(v___x_132_, 0, v___x_148_);
v___x_150_ = v___x_132_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_151_, 3, v_l_129_);
lean_ctor_set(v_reuseFailAlloc_151_, 4, v_impl_136_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
else
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_215_; 
lean_inc(v_r_143_);
lean_inc(v_v_141_);
lean_inc(v_k_140_);
lean_inc(v_size_139_);
v_isSharedCheck_215_ = !lean_is_exclusive(v_impl_136_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; lean_object* v_unused_217_; lean_object* v_unused_218_; lean_object* v_unused_219_; lean_object* v_unused_220_; 
v_unused_216_ = lean_ctor_get(v_impl_136_, 4);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_impl_136_, 3);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_impl_136_, 2);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_impl_136_, 1);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_impl_136_, 0);
lean_dec(v_unused_220_);
v___x_153_ = v_impl_136_;
v_isShared_154_ = v_isSharedCheck_215_;
goto v_resetjp_152_;
}
else
{
lean_dec(v_impl_136_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_215_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v_size_155_; lean_object* v_k_156_; lean_object* v_v_157_; lean_object* v_l_158_; lean_object* v_r_159_; lean_object* v_size_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_size_155_ = lean_ctor_get(v_l_142_, 0);
v_k_156_ = lean_ctor_get(v_l_142_, 1);
v_v_157_ = lean_ctor_get(v_l_142_, 2);
v_l_158_ = lean_ctor_get(v_l_142_, 3);
v_r_159_ = lean_ctor_get(v_l_142_, 4);
v_size_160_ = lean_ctor_get(v_r_143_, 0);
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = lean_nat_mul(v___x_161_, v_size_160_);
v___x_163_ = lean_nat_dec_lt(v_size_155_, v___x_162_);
lean_dec(v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_191_; 
lean_inc(v_r_159_);
lean_inc(v_l_158_);
lean_inc(v_v_157_);
lean_inc(v_k_156_);
v_isSharedCheck_191_ = !lean_is_exclusive(v_l_142_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; lean_object* v_unused_195_; lean_object* v_unused_196_; 
v_unused_192_ = lean_ctor_get(v_l_142_, 4);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_l_142_, 3);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_l_142_, 2);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_l_142_, 1);
lean_dec(v_unused_195_);
v_unused_196_ = lean_ctor_get(v_l_142_, 0);
lean_dec(v_unused_196_);
v___x_165_ = v_l_142_;
v_isShared_166_ = v_isSharedCheck_191_;
goto v_resetjp_164_;
}
else
{
lean_dec(v_l_142_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_191_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_181_; 
v___x_167_ = lean_nat_add(v___x_137_, v_size_138_);
v___x_168_ = lean_nat_add(v___x_167_, v_size_139_);
lean_dec(v_size_139_);
if (lean_obj_tag(v_l_158_) == 0)
{
lean_object* v_size_189_; 
v_size_189_ = lean_ctor_get(v_l_158_, 0);
lean_inc(v_size_189_);
v___y_181_ = v_size_189_;
goto v___jp_180_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___y_181_ = v___x_190_;
goto v___jp_180_;
}
v___jp_169_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = lean_nat_add(v___y_170_, v___y_172_);
lean_dec(v___y_172_);
lean_dec(v___y_170_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 4, v_r_143_);
lean_ctor_set(v___x_165_, 3, v_r_159_);
lean_ctor_set(v___x_165_, 2, v_v_141_);
lean_ctor_set(v___x_165_, 1, v_k_140_);
lean_ctor_set(v___x_165_, 0, v___x_173_);
v___x_175_ = v___x_165_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_r_159_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v_r_143_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v___x_175_);
lean_ctor_set(v___x_153_, 3, v___y_171_);
lean_ctor_set(v___x_153_, 2, v_v_157_);
lean_ctor_set(v___x_153_, 1, v_k_156_);
lean_ctor_set(v___x_153_, 0, v___x_168_);
v___x_177_ = v___x_153_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_k_156_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_v_157_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v___y_171_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = lean_nat_add(v___x_167_, v___y_181_);
lean_dec(v___y_181_);
lean_dec(v___x_167_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_l_158_);
lean_ctor_set(v___x_132_, 0, v___x_182_);
v___x_184_ = v___x_132_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v_l_129_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v_l_158_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_nat_add(v___x_137_, v_size_160_);
if (lean_obj_tag(v_r_159_) == 0)
{
lean_object* v_size_186_; 
v_size_186_ = lean_ctor_get(v_r_159_, 0);
lean_inc(v_size_186_);
v___y_170_ = v___x_185_;
v___y_171_ = v___x_184_;
v___y_172_ = v_size_186_;
goto v___jp_169_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___y_170_ = v___x_185_;
v___y_171_ = v___x_184_;
v___y_172_ = v___x_187_;
goto v___jp_169_;
}
}
}
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
lean_del_object(v___x_132_);
v___x_197_ = lean_nat_add(v___x_137_, v_size_138_);
v___x_198_ = lean_nat_add(v___x_197_, v_size_139_);
lean_dec(v_size_139_);
v___x_199_ = lean_nat_add(v___x_197_, v_size_155_);
lean_dec(v___x_197_);
lean_inc_ref(v_l_129_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_l_142_);
lean_ctor_set(v___x_153_, 3, v_l_129_);
lean_ctor_set(v___x_153_, 2, v_v_128_);
lean_ctor_set(v___x_153_, 1, v_k_127_);
lean_ctor_set(v___x_153_, 0, v___x_199_);
v___x_201_ = v___x_153_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_l_129_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_l_142_);
v___x_201_ = v_reuseFailAlloc_214_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_isSharedCheck_208_ = !lean_is_exclusive(v_l_129_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; lean_object* v_unused_213_; 
v_unused_209_ = lean_ctor_get(v_l_129_, 4);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_l_129_, 3);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_l_129_, 2);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_l_129_, 1);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_l_129_, 0);
lean_dec(v_unused_213_);
v___x_203_ = v_l_129_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_dec(v_l_129_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 4, v_r_143_);
lean_ctor_set(v___x_203_, 3, v___x_201_);
lean_ctor_set(v___x_203_, 2, v_v_141_);
lean_ctor_set(v___x_203_, 1, v_k_140_);
lean_ctor_set(v___x_203_, 0, v___x_198_);
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_207_, 4, v_r_143_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_221_; 
v_l_221_ = lean_ctor_get(v_impl_136_, 3);
lean_inc(v_l_221_);
if (lean_obj_tag(v_l_221_) == 0)
{
lean_object* v_r_222_; lean_object* v_k_223_; lean_object* v_v_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_247_; 
v_r_222_ = lean_ctor_get(v_impl_136_, 4);
v_k_223_ = lean_ctor_get(v_impl_136_, 1);
v_v_224_ = lean_ctor_get(v_impl_136_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_impl_136_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_248_ = lean_ctor_get(v_impl_136_, 3);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_impl_136_, 0);
lean_dec(v_unused_249_);
v___x_226_ = v_impl_136_;
v_isShared_227_ = v_isSharedCheck_247_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_r_222_);
lean_inc(v_v_224_);
lean_inc(v_k_223_);
lean_dec(v_impl_136_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_247_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_k_228_; lean_object* v_v_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_243_; 
v_k_228_ = lean_ctor_get(v_l_221_, 1);
v_v_229_ = lean_ctor_get(v_l_221_, 2);
v_isSharedCheck_243_ = !lean_is_exclusive(v_l_221_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_244_ = lean_ctor_get(v_l_221_, 4);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_l_221_, 3);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_l_221_, 0);
lean_dec(v_unused_246_);
v___x_231_ = v_l_221_;
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_v_229_);
lean_inc(v_k_228_);
lean_dec(v_l_221_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_222_, 2);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 4, v_r_222_);
lean_ctor_set(v___x_231_, 3, v_r_222_);
lean_ctor_set(v___x_231_, 2, v_v_128_);
lean_ctor_set(v___x_231_, 1, v_k_127_);
lean_ctor_set(v___x_231_, 0, v___x_137_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_r_222_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_r_222_);
v___x_235_ = v_reuseFailAlloc_242_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
lean_inc(v_r_222_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 3, v_r_222_);
lean_ctor_set(v___x_226_, 0, v___x_137_);
v___x_237_ = v___x_226_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_k_223_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_v_224_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_r_222_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_r_222_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_239_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v___x_237_);
lean_ctor_set(v___x_132_, 3, v___x_235_);
lean_ctor_set(v___x_132_, 2, v_v_229_);
lean_ctor_set(v___x_132_, 1, v_k_228_);
lean_ctor_set(v___x_132_, 0, v___x_233_);
v___x_239_ = v___x_132_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_k_228_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_v_229_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
else
{
lean_object* v_r_250_; 
v_r_250_ = lean_ctor_get(v_impl_136_, 4);
lean_inc(v_r_250_);
if (lean_obj_tag(v_r_250_) == 0)
{
lean_object* v_k_251_; lean_object* v_v_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_263_; 
v_k_251_ = lean_ctor_get(v_impl_136_, 1);
v_v_252_ = lean_ctor_get(v_impl_136_, 2);
v_isSharedCheck_263_ = !lean_is_exclusive(v_impl_136_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; lean_object* v_unused_265_; lean_object* v_unused_266_; 
v_unused_264_ = lean_ctor_get(v_impl_136_, 4);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_impl_136_, 3);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_impl_136_, 0);
lean_dec(v_unused_266_);
v___x_254_ = v_impl_136_;
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_v_252_);
lean_inc(v_k_251_);
lean_dec(v_impl_136_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = lean_unsigned_to_nat(3u);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v_l_221_);
lean_ctor_set(v___x_254_, 2, v_v_128_);
lean_ctor_set(v___x_254_, 1, v_k_127_);
lean_ctor_set(v___x_254_, 0, v___x_137_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_l_221_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_l_221_);
v___x_258_ = v_reuseFailAlloc_262_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_r_250_);
lean_ctor_set(v___x_132_, 3, v___x_258_);
lean_ctor_set(v___x_132_, 2, v_v_252_);
lean_ctor_set(v___x_132_, 1, v_k_251_);
lean_ctor_set(v___x_132_, 0, v___x_256_);
v___x_260_ = v___x_132_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_252_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_r_250_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_unsigned_to_nat(2u);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_impl_136_);
lean_ctor_set(v___x_132_, 3, v_r_250_);
lean_ctor_set(v___x_132_, 0, v___x_267_);
v___x_269_ = v___x_132_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v_r_250_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v_impl_136_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
else
{
lean_object* v___x_272_; 
lean_dec(v_v_128_);
lean_dec(v_k_127_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 2, v_v_124_);
lean_ctor_set(v___x_132_, 1, v_k_123_);
v___x_272_ = v___x_132_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_size_126_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_k_123_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_v_124_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_l_129_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v_r_130_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_impl_274_; lean_object* v___x_275_; 
lean_dec(v_size_126_);
v_impl_274_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_123_, v_v_124_, v_l_129_);
v___x_275_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_130_) == 0)
{
lean_object* v_size_276_; lean_object* v_size_277_; lean_object* v_k_278_; lean_object* v_v_279_; lean_object* v_l_280_; lean_object* v_r_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_size_276_ = lean_ctor_get(v_r_130_, 0);
v_size_277_ = lean_ctor_get(v_impl_274_, 0);
v_k_278_ = lean_ctor_get(v_impl_274_, 1);
v_v_279_ = lean_ctor_get(v_impl_274_, 2);
v_l_280_ = lean_ctor_get(v_impl_274_, 3);
v_r_281_ = lean_ctor_get(v_impl_274_, 4);
lean_inc(v_r_281_);
v___x_282_ = lean_unsigned_to_nat(3u);
v___x_283_ = lean_nat_mul(v___x_282_, v_size_276_);
v___x_284_ = lean_nat_dec_lt(v___x_283_, v_size_277_);
lean_dec(v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
lean_dec(v_r_281_);
v___x_285_ = lean_nat_add(v___x_275_, v_size_277_);
v___x_286_ = lean_nat_add(v___x_285_, v_size_276_);
lean_dec(v___x_285_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 3, v_impl_274_);
lean_ctor_set(v___x_132_, 0, v___x_286_);
v___x_288_ = v___x_132_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_impl_274_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_r_130_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
else
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_355_; 
lean_inc(v_l_280_);
lean_inc(v_v_279_);
lean_inc(v_k_278_);
lean_inc(v_size_277_);
v_isSharedCheck_355_ = !lean_is_exclusive(v_impl_274_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; lean_object* v_unused_357_; lean_object* v_unused_358_; lean_object* v_unused_359_; lean_object* v_unused_360_; 
v_unused_356_ = lean_ctor_get(v_impl_274_, 4);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_impl_274_, 3);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_impl_274_, 2);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_impl_274_, 1);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_impl_274_, 0);
lean_dec(v_unused_360_);
v___x_291_ = v_impl_274_;
v_isShared_292_ = v_isSharedCheck_355_;
goto v_resetjp_290_;
}
else
{
lean_dec(v_impl_274_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_355_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_size_293_; lean_object* v_size_294_; lean_object* v_k_295_; lean_object* v_v_296_; lean_object* v_l_297_; lean_object* v_r_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_size_293_ = lean_ctor_get(v_l_280_, 0);
v_size_294_ = lean_ctor_get(v_r_281_, 0);
v_k_295_ = lean_ctor_get(v_r_281_, 1);
v_v_296_ = lean_ctor_get(v_r_281_, 2);
v_l_297_ = lean_ctor_get(v_r_281_, 3);
v_r_298_ = lean_ctor_get(v_r_281_, 4);
v___x_299_ = lean_unsigned_to_nat(2u);
v___x_300_ = lean_nat_mul(v___x_299_, v_size_293_);
v___x_301_ = lean_nat_dec_lt(v_size_294_, v___x_300_);
lean_dec(v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_330_; 
lean_inc(v_r_298_);
lean_inc(v_l_297_);
lean_inc(v_v_296_);
lean_inc(v_k_295_);
v_isSharedCheck_330_ = !lean_is_exclusive(v_r_281_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; 
v_unused_331_ = lean_ctor_get(v_r_281_, 4);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_r_281_, 3);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_r_281_, 2);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_r_281_, 1);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_r_281_, 0);
lean_dec(v_unused_335_);
v___x_303_ = v_r_281_;
v_isShared_304_ = v_isSharedCheck_330_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_r_281_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_330_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___x_318_; lean_object* v___y_320_; 
v___x_305_ = lean_nat_add(v___x_275_, v_size_277_);
lean_dec(v_size_277_);
v___x_306_ = lean_nat_add(v___x_305_, v_size_276_);
lean_dec(v___x_305_);
v___x_318_ = lean_nat_add(v___x_275_, v_size_293_);
if (lean_obj_tag(v_l_297_) == 0)
{
lean_object* v_size_328_; 
v_size_328_ = lean_ctor_get(v_l_297_, 0);
lean_inc(v_size_328_);
v___y_320_ = v_size_328_;
goto v___jp_319_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___y_320_ = v___x_329_;
goto v___jp_319_;
}
v___jp_307_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_nat_add(v___y_308_, v___y_310_);
lean_dec(v___y_310_);
lean_dec(v___y_308_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 4, v_r_130_);
lean_ctor_set(v___x_303_, 3, v_r_298_);
lean_ctor_set(v___x_303_, 2, v_v_128_);
lean_ctor_set(v___x_303_, 1, v_k_127_);
lean_ctor_set(v___x_303_, 0, v___x_311_);
v___x_313_ = v___x_303_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_r_298_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_r_130_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 4, v___x_313_);
lean_ctor_set(v___x_291_, 3, v___y_309_);
lean_ctor_set(v___x_291_, 2, v_v_296_);
lean_ctor_set(v___x_291_, 1, v_k_295_);
lean_ctor_set(v___x_291_, 0, v___x_306_);
v___x_315_ = v___x_291_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v___y_309_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_nat_add(v___x_318_, v___y_320_);
lean_dec(v___y_320_);
lean_dec(v___x_318_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_l_297_);
lean_ctor_set(v___x_132_, 3, v_l_280_);
lean_ctor_set(v___x_132_, 2, v_v_279_);
lean_ctor_set(v___x_132_, 1, v_k_278_);
lean_ctor_set(v___x_132_, 0, v___x_321_);
v___x_323_ = v___x_132_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_k_278_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_v_279_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_l_280_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_l_297_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; 
v___x_324_ = lean_nat_add(v___x_275_, v_size_276_);
if (lean_obj_tag(v_r_298_) == 0)
{
lean_object* v_size_325_; 
v_size_325_ = lean_ctor_get(v_r_298_, 0);
lean_inc(v_size_325_);
v___y_308_ = v___x_324_;
v___y_309_ = v___x_323_;
v___y_310_ = v_size_325_;
goto v___jp_307_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___y_308_ = v___x_324_;
v___y_309_ = v___x_323_;
v___y_310_ = v___x_326_;
goto v___jp_307_;
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
lean_del_object(v___x_132_);
v___x_336_ = lean_nat_add(v___x_275_, v_size_277_);
lean_dec(v_size_277_);
v___x_337_ = lean_nat_add(v___x_336_, v_size_276_);
lean_dec(v___x_336_);
v___x_338_ = lean_nat_add(v___x_275_, v_size_276_);
v___x_339_ = lean_nat_add(v___x_338_, v_size_294_);
lean_dec(v___x_338_);
lean_inc_ref(v_r_130_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 4, v_r_130_);
lean_ctor_set(v___x_291_, 3, v_r_281_);
lean_ctor_set(v___x_291_, 2, v_v_128_);
lean_ctor_set(v___x_291_, 1, v_k_127_);
lean_ctor_set(v___x_291_, 0, v___x_339_);
v___x_341_ = v___x_291_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_r_281_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_r_130_);
v___x_341_ = v_reuseFailAlloc_354_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_isSharedCheck_348_ = !lean_is_exclusive(v_r_130_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; lean_object* v_unused_352_; lean_object* v_unused_353_; 
v_unused_349_ = lean_ctor_get(v_r_130_, 4);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_r_130_, 3);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_r_130_, 2);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_r_130_, 1);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_r_130_, 0);
lean_dec(v_unused_353_);
v___x_343_ = v_r_130_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_dec(v_r_130_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 4, v___x_341_);
lean_ctor_set(v___x_343_, 3, v_l_280_);
lean_ctor_set(v___x_343_, 2, v_v_279_);
lean_ctor_set(v___x_343_, 1, v_k_278_);
lean_ctor_set(v___x_343_, 0, v___x_337_);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_278_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_v_279_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_l_280_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v___x_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_361_; 
v_l_361_ = lean_ctor_get(v_impl_274_, 3);
if (lean_obj_tag(v_l_361_) == 0)
{
lean_object* v_r_362_; lean_object* v_k_363_; lean_object* v_v_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_375_; 
lean_inc_ref(v_l_361_);
v_r_362_ = lean_ctor_get(v_impl_274_, 4);
v_k_363_ = lean_ctor_get(v_impl_274_, 1);
v_v_364_ = lean_ctor_get(v_impl_274_, 2);
v_isSharedCheck_375_ = !lean_is_exclusive(v_impl_274_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_376_ = lean_ctor_get(v_impl_274_, 3);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_impl_274_, 0);
lean_dec(v_unused_377_);
v___x_366_ = v_impl_274_;
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_r_362_);
lean_inc(v_v_364_);
lean_inc(v_k_363_);
lean_dec(v_impl_274_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_362_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 3, v_r_362_);
lean_ctor_set(v___x_366_, 2, v_v_128_);
lean_ctor_set(v___x_366_, 1, v_k_127_);
lean_ctor_set(v___x_366_, 0, v___x_275_);
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_r_362_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_r_362_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v___x_370_);
lean_ctor_set(v___x_132_, 3, v_l_361_);
lean_ctor_set(v___x_132_, 2, v_v_364_);
lean_ctor_set(v___x_132_, 1, v_k_363_);
lean_ctor_set(v___x_132_, 0, v___x_368_);
v___x_372_ = v___x_132_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_l_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_r_378_; 
v_r_378_ = lean_ctor_get(v_impl_274_, 4);
lean_inc(v_r_378_);
if (lean_obj_tag(v_r_378_) == 0)
{
lean_object* v_k_379_; lean_object* v_v_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_403_; 
lean_inc(v_l_361_);
v_k_379_ = lean_ctor_get(v_impl_274_, 1);
v_v_380_ = lean_ctor_get(v_impl_274_, 2);
v_isSharedCheck_403_ = !lean_is_exclusive(v_impl_274_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_404_ = lean_ctor_get(v_impl_274_, 4);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_impl_274_, 3);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_impl_274_, 0);
lean_dec(v_unused_406_);
v___x_382_ = v_impl_274_;
v_isShared_383_ = v_isSharedCheck_403_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_v_380_);
lean_inc(v_k_379_);
lean_dec(v_impl_274_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_403_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_k_384_; lean_object* v_v_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_399_; 
v_k_384_ = lean_ctor_get(v_r_378_, 1);
v_v_385_ = lean_ctor_get(v_r_378_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v_r_378_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; lean_object* v_unused_401_; lean_object* v_unused_402_; 
v_unused_400_ = lean_ctor_get(v_r_378_, 4);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_r_378_, 3);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_r_378_, 0);
lean_dec(v_unused_402_);
v___x_387_ = v_r_378_;
v_isShared_388_ = v_isSharedCheck_399_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_v_385_);
lean_inc(v_k_384_);
lean_dec(v_r_378_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_399_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_unsigned_to_nat(3u);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 4, v_l_361_);
lean_ctor_set(v___x_387_, 3, v_l_361_);
lean_ctor_set(v___x_387_, 2, v_v_380_);
lean_ctor_set(v___x_387_, 1, v_k_379_);
lean_ctor_set(v___x_387_, 0, v___x_275_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_379_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_380_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_l_361_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_l_361_);
v___x_391_ = v_reuseFailAlloc_398_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 4, v_l_361_);
lean_ctor_set(v___x_382_, 2, v_v_128_);
lean_ctor_set(v___x_382_, 1, v_k_127_);
lean_ctor_set(v___x_382_, 0, v___x_275_);
v___x_393_ = v___x_382_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_l_361_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_l_361_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v___x_393_);
lean_ctor_set(v___x_132_, 3, v___x_391_);
lean_ctor_set(v___x_132_, 2, v_v_385_);
lean_ctor_set(v___x_132_, 1, v_k_384_);
lean_ctor_set(v___x_132_, 0, v___x_389_);
v___x_395_ = v___x_132_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_k_384_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_v_385_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_unsigned_to_nat(2u);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_r_378_);
lean_ctor_set(v___x_132_, 3, v_impl_274_);
lean_ctor_set(v___x_132_, 0, v___x_407_);
v___x_409_ = v___x_132_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_impl_274_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_r_378_);
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
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_k_123_);
lean_ctor_set(v___x_413_, 2, v_v_124_);
lean_ctor_set(v___x_413_, 3, v_t_125_);
lean_ctor_set(v___x_413_, 4, v_t_125_);
return v___x_413_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* v_k_414_, lean_object* v_t_415_){
_start:
{
if (lean_obj_tag(v_t_415_) == 0)
{
lean_object* v_k_416_; lean_object* v_l_417_; lean_object* v_r_418_; uint8_t v___x_419_; 
v_k_416_ = lean_ctor_get(v_t_415_, 1);
v_l_417_ = lean_ctor_get(v_t_415_, 3);
v_r_418_ = lean_ctor_get(v_t_415_, 4);
v___x_419_ = lean_nat_dec_lt(v_k_414_, v_k_416_);
if (v___x_419_ == 0)
{
uint8_t v___x_420_; 
v___x_420_ = lean_nat_dec_eq(v_k_414_, v_k_416_);
if (v___x_420_ == 0)
{
v_t_415_ = v_r_418_;
goto _start;
}
else
{
return v___x_420_;
}
}
else
{
v_t_415_ = v_l_417_;
goto _start;
}
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* v_k_424_, lean_object* v_t_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_424_, v_t_425_);
lean_dec(v_t_425_);
lean_dec(v_k_424_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* v_i_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_443_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_st_ref_get(v_a_432_);
v___x_449_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_430_, v___x_448_);
lean_dec(v___x_448_);
if (v___x_449_ == 0)
{
v___y_443_ = v_a_432_;
goto v___jp_442_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__0));
v___x_451_ = l_Nat_reprFast(v_i_430_);
v___x_452_ = lean_string_append(v___x_450_, v___x_451_);
lean_dec_ref(v___x_451_);
v___x_453_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__1));
v___x_454_ = lean_string_append(v___x_452_, v___x_453_);
v___x_455_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_454_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
return v___x_455_;
}
v___jp_436_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_st_ref_put(v___y_438_, v___y_439_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___y_437_);
return v___x_441_;
}
v___jp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_st_ref_take(v___y_443_);
v___x_445_ = lean_box(0);
v___x_446_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_430_, v___x_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_i_430_, v___x_445_, v___x_444_);
v___y_437_ = v___x_445_;
v___y_438_ = v___y_443_;
v___y_439_ = v___x_447_;
goto v___jp_436_;
}
else
{
lean_dec(v_i_430_);
v___y_437_ = v___x_445_;
v___y_438_ = v___y_443_;
v___y_439_ = v___x_444_;
goto v___jp_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* v_i_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_IR_Checker_markIndex(v_i_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_462_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(lean_object* v_00_u03b2_463_, lean_object* v_k_464_, lean_object* v_t_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_464_, v_t_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* v_00_u03b2_467_, lean_object* v_k_468_, lean_object* v_t_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(v_00_u03b2_467_, v_k_468_, v_t_469_);
lean_dec(v_t_469_);
lean_dec(v_k_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(lean_object* v_00_u03b2_472_, lean_object* v_k_473_, lean_object* v_v_474_, lean_object* v_t_475_, lean_object* v_hl_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_473_, v_v_474_, v_t_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* v_x_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_IR_Checker_markIndex(v_x_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* v_x_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_IR_Checker_markVar(v_x_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* v_j_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_IR_Checker_markIndex(v_j_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* v_j_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_IR_Checker_markJP(v_j_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* v_c_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_514_; lean_object* v_env_515_; lean_object* v_decls_516_; lean_object* v___x_517_; 
v___x_514_ = lean_st_ref_get(v_a_512_);
v_env_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_env_515_);
lean_dec(v___x_514_);
v_decls_516_ = lean_ctor_get(v_a_509_, 2);
lean_inc(v_c_508_);
v___x_517_ = l_Lean_IR_findEnvDecl_x27(v_env_515_, v_c_508_, v_decls_516_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_518_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
v___x_519_ = 1;
v___x_520_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_508_, v___x_519_);
v___x_521_ = lean_string_append(v___x_518_, v___x_520_);
lean_dec_ref(v___x_520_);
v___x_522_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
v___x_523_ = lean_string_append(v___x_521_, v___x_522_);
v___x_524_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_523_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
return v___x_524_;
}
else
{
lean_object* v_val_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_c_508_);
v_val_525_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_517_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_val_525_);
lean_dec(v___x_517_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 0);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_val_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* v_c_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_IR_Checker_getDecl(v_c_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* v_x_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
uint8_t v___y_550_; lean_object* v_localCtx_561_; uint8_t v___x_562_; 
v_localCtx_561_ = lean_ctor_get(v_a_544_, 0);
v___x_562_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_561_, v_x_543_);
if (v___x_562_ == 0)
{
uint8_t v___x_563_; 
v___x_563_ = l_Lean_IR_LocalContext_isParam(v_localCtx_561_, v_x_543_);
v___y_550_ = v___x_563_;
goto v___jp_549_;
}
else
{
v___y_550_ = v___x_562_;
goto v___jp_549_;
}
v___jp_549_:
{
if (v___y_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_551_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_552_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_553_ = l_Nat_reprFast(v_x_543_);
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = lean_string_append(v___x_551_, v___x_554_);
lean_dec_ref(v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_557_ = lean_string_append(v___x_555_, v___x_556_);
v___x_558_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_557_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_x_543_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_IR_Checker_checkVar(v_x_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_localCtx_579_; uint8_t v___x_580_; 
v_localCtx_579_ = lean_ctor_get(v_a_574_, 0);
v___x_580_ = l_Lean_IR_LocalContext_isJP(v_localCtx_579_, v_j_573_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_581_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_582_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_583_ = l_Nat_reprFast(v_j_573_);
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
lean_dec_ref(v___x_583_);
v___x_585_ = lean_string_append(v___x_581_, v___x_584_);
lean_dec_ref(v___x_584_);
v___x_586_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
v___x_588_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_587_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v_j_573_);
v___x_589_ = lean_box(0);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_IR_Checker_checkJP(v_j_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
if (lean_obj_tag(v_a_598_) == 0)
{
lean_object* v_id_604_; lean_object* v___x_605_; 
v_id_604_ = lean_ctor_get(v_a_598_, 0);
lean_inc(v_id_604_);
lean_dec_ref_known(v_a_598_, 1);
v___x_605_ = l_Lean_IR_Checker_checkVar(v_id_604_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_IR_Checker_checkArg(v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_615_, size_t v_i_616_, size_t v_stop_617_, lean_object* v_b_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_624_; 
v___x_624_ = lean_usize_dec_eq(v_i_616_, v_stop_617_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_array_uget_borrowed(v_as_615_, v_i_616_);
lean_inc(v___x_625_);
v___x_626_ = l_Lean_IR_Checker_checkArg(v___x_625_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; size_t v___x_628_; size_t v___x_629_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_616_, v___x_628_);
v_i_616_ = v___x_629_;
v_b_618_ = v_a_627_;
goto _start;
}
else
{
return v___x_626_;
}
}
else
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v_b_618_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_632_, lean_object* v_i_633_, lean_object* v_stop_634_, lean_object* v_b_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
size_t v_i_boxed_641_; size_t v_stop_boxed_642_; lean_object* v_res_643_; 
v_i_boxed_641_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_stop_boxed_642_ = lean_unbox_usize(v_stop_634_);
lean_dec(v_stop_634_);
v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_632_, v_i_boxed_641_, v_stop_boxed_642_, v_b_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v_as_632_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_array_get_size(v_as_644_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_nat_dec_lt(v___x_650_, v___x_651_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
return v___x_654_;
}
else
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_le(v___x_651_, v___x_651_);
if (v___x_655_ == 0)
{
if (v___x_653_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_652_);
return v___x_656_;
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = ((size_t)0ULL);
v___x_658_ = lean_usize_of_nat(v___x_651_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_644_, v___x_657_, v___x_658_, v___x_652_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
return v___x_659_;
}
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_651_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_644_, v___x_660_, v___x_661_, v___x_652_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_IR_Checker_checkArgs(v_as_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec_ref(v_as_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_671_, lean_object* v_ty_u2082_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_671_, v_ty_u2082_672_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_680_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_679_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_683_, lean_object* v_ty_u2082_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_683_, v_ty_u2082_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_ty_u2082_684_);
lean_dec(v_ty_u2081_683_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_693_, lean_object* v_p_694_, lean_object* v_suffix_x3f_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
lean_inc(v_ty_693_);
v___x_701_ = lean_apply_1(v_p_694_, v_ty_693_);
v___x_702_ = lean_unbox(v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_msg_710_; 
v___x_703_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_704_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_693_);
v___x_705_ = l_Std_Format_defWidth;
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = l_Std_Format_pretty(v___x_704_, v___x_705_, v___x_706_, v___x_706_);
v___x_708_ = lean_string_append(v___x_703_, v___x_707_);
lean_dec_ref(v___x_707_);
v___x_709_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_710_ = lean_string_append(v___x_708_, v___x_709_);
if (lean_obj_tag(v_suffix_x3f_695_) == 1)
{
lean_object* v_val_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_msg_714_; lean_object* v___x_715_; 
v_val_711_ = lean_ctor_get(v_suffix_x3f_695_, 0);
v___x_712_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_713_ = lean_string_append(v_msg_710_, v___x_712_);
v_msg_714_ = lean_string_append(v___x_713_, v_val_711_);
v___x_715_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_714_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_710_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
return v___x_716_;
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v_ty_693_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_719_, lean_object* v_p_720_, lean_object* v_suffix_x3f_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_IR_Checker_checkType(v_ty_719_, v_p_720_, v_suffix_x3f_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_suffix_x3f_721_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = l_Lean_IR_IRType_isObj(v_ty_729_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_msg_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_msg_747_; lean_object* v___x_748_; 
v___x_736_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_737_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_738_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_729_);
v___x_739_ = l_Std_Format_defWidth;
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = l_Std_Format_pretty(v___x_738_, v___x_739_, v___x_740_, v___x_740_);
v___x_742_ = lean_string_append(v___x_737_, v___x_741_);
lean_dec_ref(v___x_741_);
v___x_743_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_744_ = lean_string_append(v___x_742_, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_746_ = lean_string_append(v_msg_744_, v___x_745_);
v_msg_747_ = lean_string_append(v___x_746_, v___x_736_);
v___x_748_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_747_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_748_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v_ty_729_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_IR_Checker_checkObjType(v_ty_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = l_Lean_IR_IRType_isScalar(v_ty_759_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_msg_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_msg_777_; lean_object* v___x_778_; 
v___x_766_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_767_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_768_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_759_);
v___x_769_ = l_Std_Format_defWidth;
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = l_Std_Format_pretty(v___x_768_, v___x_769_, v___x_770_, v___x_770_);
v___x_772_ = lean_string_append(v___x_767_, v___x_771_);
lean_dec_ref(v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_774_ = lean_string_append(v___x_772_, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_776_ = lean_string_append(v_msg_774_, v___x_775_);
v_msg_777_ = lean_string_append(v___x_776_, v___x_766_);
v___x_778_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_777_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec(v_ty_759_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_IR_Checker_checkScalarType(v_ty_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_localCtx_794_; lean_object* v___x_795_; 
v_localCtx_794_ = lean_ctor_get(v_a_789_, 0);
v___x_795_ = l_Lean_IR_LocalContext_getType(v_localCtx_794_, v_x_788_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_796_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_797_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_798_ = l_Nat_reprFast(v_x_788_);
v___x_799_ = lean_string_append(v___x_797_, v___x_798_);
lean_dec_ref(v___x_798_);
v___x_800_ = lean_string_append(v___x_796_, v___x_799_);
lean_dec_ref(v___x_799_);
v___x_801_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_802_ = lean_string_append(v___x_800_, v___x_801_);
v___x_803_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_802_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_x_788_);
v_val_804_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_795_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_val_804_);
lean_dec(v___x_795_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 0);
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_val_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_IR_Checker_getType(v_x_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_819_, lean_object* v_p_820_, lean_object* v_suffix_x3f_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_IR_Checker_getType(v_x_819_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_852_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_852_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_852_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_852_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; uint8_t v___x_833_; 
lean_inc(v_a_828_);
v___x_832_ = lean_apply_1(v_p_820_, v_a_828_);
v___x_833_ = lean_unbox(v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v_msg_841_; 
lean_del_object(v___x_830_);
v___x_834_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_835_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_828_);
v___x_836_ = l_Std_Format_defWidth;
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = l_Std_Format_pretty(v___x_835_, v___x_836_, v___x_837_, v___x_837_);
v___x_839_ = lean_string_append(v___x_834_, v___x_838_);
lean_dec_ref(v___x_838_);
v___x_840_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_841_ = lean_string_append(v___x_839_, v___x_840_);
if (lean_obj_tag(v_suffix_x3f_821_) == 1)
{
lean_object* v_val_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_msg_845_; lean_object* v___x_846_; 
v_val_842_ = lean_ctor_get(v_suffix_x3f_821_, 0);
v___x_843_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_844_ = lean_string_append(v_msg_841_, v___x_843_);
v_msg_845_ = lean_string_append(v___x_844_, v_val_842_);
v___x_846_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_845_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_841_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_847_;
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_850_; 
lean_dec(v_a_828_);
v___x_848_ = lean_box(0);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_848_);
v___x_850_ = v___x_830_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec_ref(v_p_820_);
v_a_853_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_827_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_827_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_861_, lean_object* v_p_862_, lean_object* v_suffix_x3f_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_IR_Checker_checkVarType(v_x_861_, v_p_862_, v_suffix_x3f_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_suffix_x3f_863_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_877_ = l_Lean_IR_Checker_getType(v_x_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_899_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_899_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_899_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_899_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
uint8_t v___x_882_; 
v___x_882_ = l_Lean_IR_IRType_isObj(v_a_878_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_msg_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_msg_893_; lean_object* v___x_894_; 
lean_del_object(v___x_880_);
v___x_883_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_884_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_878_);
v___x_885_ = l_Std_Format_defWidth;
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = l_Std_Format_pretty(v___x_884_, v___x_885_, v___x_886_, v___x_886_);
v___x_888_ = lean_string_append(v___x_883_, v___x_887_);
lean_dec_ref(v___x_887_);
v___x_889_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_890_ = lean_string_append(v___x_888_, v___x_889_);
v___x_891_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_892_ = lean_string_append(v_msg_890_, v___x_891_);
v_msg_893_ = lean_string_append(v___x_892_, v___x_876_);
v___x_894_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_893_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; lean_object* v___x_897_; 
lean_dec(v_a_878_);
v___x_895_ = lean_box(0);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_895_);
v___x_897_ = v___x_880_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_a_900_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_877_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_877_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_IR_Checker_checkObjVar(v_x_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_922_ = l_Lean_IR_Checker_getType(v_x_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_944_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_944_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_944_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_944_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_IR_IRType_isScalar(v_a_923_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_msg_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_msg_938_; lean_object* v___x_939_; 
lean_del_object(v___x_925_);
v___x_928_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_929_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_923_);
v___x_930_ = l_Std_Format_defWidth;
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = l_Std_Format_pretty(v___x_929_, v___x_930_, v___x_931_, v___x_931_);
v___x_933_ = lean_string_append(v___x_928_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_935_ = lean_string_append(v___x_933_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_937_ = lean_string_append(v_msg_935_, v___x_936_);
v_msg_938_ = lean_string_append(v___x_937_, v___x_921_);
v___x_939_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_938_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_942_; 
lean_dec(v_a_923_);
v___x_940_ = lean_box(0);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_940_);
v___x_942_ = v___x_925_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_a_945_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_922_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_922_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_IR_Checker_checkScalarVar(v_x_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_964_, lean_object* v_ys_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v___x_971_; 
lean_inc(v_c_964_);
v___x_971_ = l_Lean_IR_Checker_getDecl(v_c_964_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = lean_array_get_size(v_ys_965_);
v___x_974_ = l_Lean_IR_Decl_params(v_a_972_);
lean_dec(v_a_972_);
v___x_975_ = lean_array_get_size(v___x_974_);
lean_dec_ref(v___x_974_);
v___x_976_ = lean_nat_dec_eq(v___x_973_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; uint8_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_977_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_978_ = 1;
v___x_979_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_964_, v___x_978_);
v___x_980_ = lean_string_append(v___x_977_, v___x_979_);
lean_dec_ref(v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_982_ = lean_string_append(v___x_980_, v___x_981_);
v___x_983_ = l_Nat_reprFast(v___x_973_);
v___x_984_ = lean_string_append(v___x_982_, v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_986_ = lean_string_append(v___x_984_, v___x_985_);
v___x_987_ = l_Nat_reprFast(v___x_975_);
v___x_988_ = lean_string_append(v___x_986_, v___x_987_);
lean_dec_ref(v___x_987_);
v___x_989_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
v___x_991_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_990_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; 
lean_dec(v_c_964_);
v___x_992_ = l_Lean_IR_Checker_checkArgs(v_ys_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
return v___x_992_;
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_c_964_);
v_a_993_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_971_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_971_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_1001_, lean_object* v_ys_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_IR_Checker_checkFullApp(v_c_1001_, v_ys_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec_ref(v_ys_1002_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1012_, lean_object* v_ys_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; 
lean_inc(v_c_1012_);
v___x_1019_ = l_Lean_IR_Checker_getDecl(v_c_1012_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = lean_array_get_size(v_ys_1013_);
v___x_1022_ = l_Lean_IR_Decl_params(v_a_1020_);
lean_dec(v_a_1020_);
v___x_1023_ = lean_array_get_size(v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = lean_nat_dec_lt(v___x_1021_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1025_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1026_ = 1;
v___x_1027_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1012_, v___x_1026_);
v___x_1028_ = lean_string_append(v___x_1025_, v___x_1027_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1030_ = lean_string_append(v___x_1028_, v___x_1029_);
v___x_1031_ = l_Nat_reprFast(v___x_1021_);
v___x_1032_ = lean_string_append(v___x_1030_, v___x_1031_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1034_ = lean_string_append(v___x_1032_, v___x_1033_);
v___x_1035_ = l_Nat_reprFast(v___x_1023_);
v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1036_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; 
lean_dec(v_c_1012_);
v___x_1038_ = l_Lean_IR_Checker_checkArgs(v_ys_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
return v___x_1038_;
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_c_1012_);
v_a_1039_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1019_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1019_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1047_, lean_object* v_ys_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_IR_Checker_checkPartialApp(v_c_1047_, v_ys_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec_ref(v_ys_1048_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1062_, lean_object* v_e_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
switch(lean_obj_tag(v_e_1063_))
{
case 0:
{
lean_object* v_i_1069_; lean_object* v_ys_1070_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v_name_1081_; lean_object* v_cidx_1082_; lean_object* v_size_1083_; lean_object* v_usize_1084_; lean_object* v_ssize_1085_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_i_1069_ = lean_ctor_get(v_e_1063_, 0);
lean_inc_ref(v_i_1069_);
v_ys_1070_ = lean_ctor_get(v_e_1063_, 1);
lean_inc_ref(v_ys_1070_);
lean_dec_ref_known(v_e_1063_, 2);
v_name_1081_ = lean_ctor_get(v_i_1069_, 0);
v_cidx_1082_ = lean_ctor_get(v_i_1069_, 1);
v_size_1083_ = lean_ctor_get(v_i_1069_, 2);
v_usize_1084_ = lean_ctor_get(v_i_1069_, 3);
v_ssize_1085_ = lean_ctor_get(v_i_1069_, 4);
v___x_1117_ = l_Lean_maxCtorTag;
v___x_1118_ = lean_nat_dec_lt(v___x_1117_, v_cidx_1082_);
if (v___x_1118_ == 0)
{
v___y_1104_ = v_a_1064_;
v___y_1105_ = v_a_1065_;
v___y_1106_ = v_a_1066_;
v___y_1107_ = v_a_1067_;
goto v___jp_1103_;
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Lean_IR_CtorInfo_isRef(v_i_1069_);
if (v___x_1119_ == 0)
{
v___y_1104_ = v_a_1064_;
v___y_1105_ = v_a_1065_;
v___y_1106_ = v_a_1066_;
v___y_1107_ = v_a_1067_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_inc(v_name_1081_);
lean_dec_ref(v_ys_1070_);
lean_dec_ref(v_i_1069_);
lean_dec(v_ty_1062_);
v___x_1120_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1081_, v___x_1119_);
v___x_1122_ = lean_string_append(v___x_1120_, v___x_1121_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1124_ = lean_string_append(v___x_1122_, v___x_1123_);
v___x_1125_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1124_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1125_;
}
}
v___jp_1071_:
{
uint8_t v___x_1076_; 
v___x_1076_ = l_Lean_IR_CtorInfo_isRef(v_i_1069_);
lean_dec_ref(v_i_1069_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec_ref(v_ys_1070_);
lean_dec(v_ty_1062_);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v___x_1080_; 
lean_dec_ref_known(v___x_1079_, 1);
v___x_1080_ = l_Lean_IR_Checker_checkArgs(v_ys_1070_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec_ref(v_ys_1070_);
return v___x_1080_;
}
else
{
lean_dec_ref(v_ys_1070_);
return v___x_1079_;
}
}
}
v___jp_1086_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1091_ = l_Lean_usizeSize;
v___x_1092_ = lean_nat_mul(v_usize_1084_, v___x_1091_);
v___x_1093_ = lean_nat_add(v_ssize_1085_, v___x_1092_);
lean_dec(v___x_1092_);
v___x_1094_ = l_Lean_maxCtorScalarsSize;
v___x_1095_ = lean_nat_dec_lt(v___x_1093_, v___x_1094_);
lean_dec(v___x_1093_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_inc(v_name_1081_);
lean_dec_ref(v_ys_1070_);
lean_dec_ref(v_i_1069_);
lean_dec(v_ty_1062_);
v___x_1096_ = 1;
v___x_1097_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1098_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1081_, v___x_1096_);
v___x_1099_ = lean_string_append(v___x_1097_, v___x_1098_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1101_ = lean_string_append(v___x_1099_, v___x_1100_);
v___x_1102_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1101_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1102_;
}
else
{
v___y_1072_ = v___y_1087_;
v___y_1073_ = v___y_1088_;
v___y_1074_ = v___y_1089_;
v___y_1075_ = v___y_1090_;
goto v___jp_1071_;
}
}
v___jp_1103_:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = l_Lean_maxCtorFields;
v___x_1109_ = lean_nat_dec_lt(v_size_1083_, v___x_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_inc(v_name_1081_);
lean_dec_ref(v_ys_1070_);
lean_dec_ref(v_i_1069_);
lean_dec(v_ty_1062_);
v___x_1110_ = 1;
v___x_1111_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1112_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1081_, v___x_1110_);
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1115_ = lean_string_append(v___x_1113_, v___x_1114_);
v___x_1116_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1115_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1116_;
}
else
{
v___y_1087_ = v___y_1104_;
v___y_1088_ = v___y_1105_;
v___y_1089_ = v___y_1106_;
v___y_1090_ = v___y_1107_;
goto v___jp_1086_;
}
}
}
case 1:
{
lean_object* v_x_1126_; lean_object* v___x_1127_; 
v_x_1126_ = lean_ctor_get(v_e_1063_, 1);
lean_inc(v_x_1126_);
lean_dec_ref_known(v_e_1063_, 2);
v___x_1127_ = l_Lean_IR_Checker_checkObjVar(v_x_1126_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref_known(v___x_1127_, 1);
v___x_1128_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1128_;
}
else
{
lean_dec(v_ty_1062_);
return v___x_1127_;
}
}
case 2:
{
lean_object* v_x_1129_; lean_object* v_ys_1130_; lean_object* v___x_1131_; 
v_x_1129_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_x_1129_);
v_ys_1130_ = lean_ctor_get(v_e_1063_, 2);
lean_inc_ref(v_ys_1130_);
lean_dec_ref_known(v_e_1063_, 3);
v___x_1131_ = l_Lean_IR_Checker_checkObjVar(v_x_1129_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1131_, 1);
v___x_1132_ = l_Lean_IR_Checker_checkArgs(v_ys_1130_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec_ref(v_ys_1130_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; 
lean_dec_ref_known(v___x_1132_, 1);
v___x_1133_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1133_;
}
else
{
lean_dec(v_ty_1062_);
return v___x_1132_;
}
}
else
{
lean_dec_ref(v_ys_1130_);
lean_dec(v_ty_1062_);
return v___x_1131_;
}
}
case 3:
{
lean_object* v_i_1134_; lean_object* v_x_1135_; lean_object* v___x_1136_; 
v_i_1134_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_i_1134_);
v_x_1135_ = lean_ctor_get(v_e_1063_, 1);
lean_inc(v_x_1135_);
lean_dec_ref_known(v_e_1063_, 2);
v___x_1136_ = l_Lean_IR_Checker_getType(v_x_1135_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1182_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1182_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1182_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
switch(lean_obj_tag(v_a_1137_))
{
case 7:
{
lean_object* v___x_1141_; 
lean_del_object(v___x_1139_);
lean_dec(v_i_1134_);
v___x_1141_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1141_;
}
case 8:
{
lean_object* v___x_1142_; 
lean_del_object(v___x_1139_);
lean_dec(v_i_1134_);
v___x_1142_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1142_;
}
case 10:
{
lean_object* v_types_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_types_1143_ = lean_ctor_get(v_a_1137_, 1);
lean_inc_ref(v_types_1143_);
lean_dec_ref_known(v_a_1137_, 2);
v___x_1144_ = lean_array_get_size(v_types_1143_);
v___x_1145_ = lean_nat_dec_lt(v_i_1134_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec_ref(v_types_1143_);
lean_del_object(v___x_1139_);
lean_dec(v_i_1134_);
lean_dec(v_ty_1062_);
v___x_1146_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1147_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1146_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = lean_array_fget(v_types_1143_, v_i_1134_);
lean_dec(v_i_1134_);
lean_dec_ref(v_types_1143_);
v___x_1149_ = l_Lean_IR_instBEqIRType_beq(v___x_1148_, v_ty_1062_);
lean_dec(v_ty_1062_);
lean_dec(v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_del_object(v___x_1139_);
v___x_1150_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1151_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1150_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_box(0);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1152_);
v___x_1154_ = v___x_1139_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
case 11:
{
lean_object* v_types_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v_types_1156_ = lean_ctor_get(v_a_1137_, 1);
lean_inc_ref(v_types_1156_);
lean_dec_ref_known(v_a_1137_, 2);
v___x_1157_ = lean_array_get_size(v_types_1156_);
v___x_1158_ = lean_nat_dec_lt(v_i_1134_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref(v_types_1156_);
lean_del_object(v___x_1139_);
lean_dec(v_i_1134_);
lean_dec(v_ty_1062_);
v___x_1159_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1160_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1159_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = lean_array_fget(v_types_1156_, v_i_1134_);
lean_dec(v_i_1134_);
lean_dec_ref(v_types_1156_);
v___x_1162_ = l_Lean_IR_instBEqIRType_beq(v___x_1161_, v_ty_1062_);
lean_dec(v_ty_1062_);
lean_dec(v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_del_object(v___x_1139_);
v___x_1163_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1164_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1163_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1165_);
v___x_1167_ = v___x_1139_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
case 12:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_dec(v_i_1134_);
lean_dec(v_ty_1062_);
v___x_1169_ = lean_box(0);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1169_);
v___x_1171_ = v___x_1139_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
default: 
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_del_object(v___x_1139_);
lean_dec(v_i_1134_);
lean_dec(v_ty_1062_);
v___x_1173_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1174_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1137_);
v___x_1175_ = l_Std_Format_defWidth;
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = l_Std_Format_pretty(v___x_1174_, v___x_1175_, v___x_1176_, v___x_1176_);
v___x_1178_ = lean_string_append(v___x_1173_, v___x_1177_);
lean_dec_ref(v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1180_ = lean_string_append(v___x_1178_, v___x_1179_);
v___x_1181_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1180_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1181_;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v_i_1134_);
lean_dec(v_ty_1062_);
v_a_1183_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1136_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1136_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
case 4:
{
lean_object* v_x_1191_; lean_object* v___x_1192_; 
v_x_1191_ = lean_ctor_get(v_e_1063_, 1);
lean_inc(v_x_1191_);
lean_dec_ref_known(v_e_1063_, 2);
v___x_1192_ = l_Lean_IR_Checker_checkObjVar(v_x_1191_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1211_; 
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v___x_1192_, 0);
lean_dec(v_unused_1212_);
v___x_1194_ = v___x_1192_;
v_isShared_1195_ = v_isSharedCheck_1211_;
goto v_resetjp_1193_;
}
else
{
lean_dec(v___x_1192_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1211_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_box(5);
v___x_1197_ = l_Lean_IR_instBEqIRType_beq(v_ty_1062_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_msg_1205_; lean_object* v___x_1206_; 
lean_del_object(v___x_1194_);
v___x_1198_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1199_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1062_);
v___x_1200_ = l_Std_Format_defWidth;
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = l_Std_Format_pretty(v___x_1199_, v___x_1200_, v___x_1201_, v___x_1201_);
v___x_1203_ = lean_string_append(v___x_1198_, v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1205_ = lean_string_append(v___x_1203_, v___x_1204_);
v___x_1206_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1205_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_dec(v_ty_1062_);
v___x_1207_ = lean_box(0);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1207_);
v___x_1209_ = v___x_1194_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_dec(v_ty_1062_);
return v___x_1192_;
}
}
case 5:
{
lean_object* v_x_1213_; lean_object* v___x_1214_; 
v_x_1213_ = lean_ctor_get(v_e_1063_, 2);
lean_inc(v_x_1213_);
lean_dec_ref_known(v_e_1063_, 3);
v___x_1214_ = l_Lean_IR_Checker_checkObjVar(v_x_1213_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1215_; 
lean_dec_ref_known(v___x_1214_, 1);
v___x_1215_ = l_Lean_IR_Checker_checkScalarType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1215_;
}
else
{
lean_dec(v_ty_1062_);
return v___x_1214_;
}
}
case 6:
{
lean_object* v_c_1216_; lean_object* v_ys_1217_; lean_object* v___x_1218_; 
lean_dec(v_ty_1062_);
v_c_1216_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_c_1216_);
v_ys_1217_ = lean_ctor_get(v_e_1063_, 1);
lean_inc_ref(v_ys_1217_);
lean_dec_ref_known(v_e_1063_, 2);
v___x_1218_ = l_Lean_IR_Checker_checkFullApp(v_c_1216_, v_ys_1217_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec_ref(v_ys_1217_);
return v___x_1218_;
}
case 7:
{
lean_object* v_c_1219_; lean_object* v_ys_1220_; lean_object* v___x_1221_; 
v_c_1219_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_c_1219_);
v_ys_1220_ = lean_ctor_get(v_e_1063_, 1);
lean_inc_ref(v_ys_1220_);
lean_dec_ref_known(v_e_1063_, 2);
v___x_1221_ = l_Lean_IR_Checker_checkPartialApp(v_c_1219_, v_ys_1220_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec_ref(v_ys_1220_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref_known(v___x_1221_, 1);
v___x_1222_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1222_;
}
else
{
lean_dec(v_ty_1062_);
return v___x_1221_;
}
}
case 8:
{
lean_object* v_x_1223_; lean_object* v_ys_1224_; lean_object* v___x_1225_; 
v_x_1223_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_x_1223_);
v_ys_1224_ = lean_ctor_get(v_e_1063_, 1);
lean_inc_ref(v_ys_1224_);
lean_dec_ref_known(v_e_1063_, 2);
v___x_1225_ = l_Lean_IR_Checker_checkObjVar(v_x_1223_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref_known(v___x_1225_, 1);
v___x_1226_ = l_Lean_IR_Checker_checkArgs(v_ys_1224_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec_ref(v_ys_1224_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; 
lean_dec_ref_known(v___x_1226_, 1);
v___x_1227_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1227_;
}
else
{
lean_dec(v_ty_1062_);
return v___x_1226_;
}
}
else
{
lean_dec_ref(v_ys_1224_);
lean_dec(v_ty_1062_);
return v___x_1225_;
}
}
case 9:
{
lean_object* v_ty_1228_; lean_object* v_x_1229_; lean_object* v___x_1230_; 
v_ty_1228_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_ty_1228_);
v_x_1229_ = lean_ctor_get(v_e_1063_, 1);
lean_inc(v_x_1229_);
lean_dec_ref_known(v_e_1063_, 2);
v___x_1230_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1231_; 
lean_dec_ref_known(v___x_1230_, 1);
lean_inc(v_x_1229_);
v___x_1231_ = l_Lean_IR_Checker_checkScalarVar(v_x_1229_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; 
lean_dec_ref_known(v___x_1231_, 1);
v___x_1232_ = l_Lean_IR_Checker_getType(v_x_1229_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1251_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1251_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1251_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Lean_IR_instBEqIRType_beq(v_a_1233_, v_ty_1228_);
lean_dec(v_ty_1228_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_msg_1245_; lean_object* v___x_1246_; 
lean_del_object(v___x_1235_);
v___x_1238_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1239_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1233_);
v___x_1240_ = l_Std_Format_defWidth;
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = l_Std_Format_pretty(v___x_1239_, v___x_1240_, v___x_1241_, v___x_1241_);
v___x_1243_ = lean_string_append(v___x_1238_, v___x_1242_);
lean_dec_ref(v___x_1242_);
v___x_1244_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1245_ = lean_string_append(v___x_1243_, v___x_1244_);
v___x_1246_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1245_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1246_;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec(v_a_1233_);
v___x_1247_ = lean_box(0);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1247_);
v___x_1249_ = v___x_1235_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_ty_1228_);
v_a_1252_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1232_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1232_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
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
lean_dec(v_x_1229_);
lean_dec(v_ty_1228_);
return v___x_1231_;
}
}
else
{
lean_dec(v_x_1229_);
lean_dec(v_ty_1228_);
return v___x_1230_;
}
}
case 10:
{
lean_object* v_x_1260_; lean_object* v___x_1261_; 
v_x_1260_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_x_1260_);
lean_dec_ref_known(v_e_1063_, 1);
v___x_1261_ = l_Lean_IR_Checker_checkScalarType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref_known(v___x_1261_, 1);
v___x_1262_ = l_Lean_IR_Checker_checkObjVar(v_x_1260_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1262_;
}
else
{
lean_dec(v_x_1260_);
return v___x_1261_;
}
}
case 11:
{
lean_object* v_v_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1272_; 
v_v_1263_ = lean_ctor_get(v_e_1063_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_e_1063_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1265_ = v_e_1063_;
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_v_1263_);
lean_dec(v_e_1063_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
if (lean_obj_tag(v_v_1263_) == 1)
{
lean_object* v___x_1267_; 
lean_dec_ref_known(v_v_1263_, 1);
lean_del_object(v___x_1265_);
v___x_1267_ = l_Lean_IR_Checker_checkObjType(v_ty_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_dec_ref(v_v_1263_);
lean_dec(v_ty_1062_);
v___x_1268_ = lean_box(0);
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1268_);
v___x_1270_ = v___x_1265_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
default: 
{
lean_object* v_x_1273_; lean_object* v___x_1274_; 
v_x_1273_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_x_1273_);
lean_dec_ref_known(v_e_1063_, 1);
v___x_1274_ = l_Lean_IR_Checker_checkObjVar(v_x_1273_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1293_; 
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1274_, 0);
lean_dec(v_unused_1294_);
v___x_1276_ = v___x_1274_;
v_isShared_1277_ = v_isSharedCheck_1293_;
goto v_resetjp_1275_;
}
else
{
lean_dec(v___x_1274_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1293_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = lean_box(1);
v___x_1279_ = l_Lean_IR_instBEqIRType_beq(v_ty_1062_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_msg_1287_; lean_object* v___x_1288_; 
lean_del_object(v___x_1276_);
v___x_1280_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1281_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1062_);
v___x_1282_ = l_Std_Format_defWidth;
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = l_Std_Format_pretty(v___x_1281_, v___x_1282_, v___x_1283_, v___x_1283_);
v___x_1285_ = lean_string_append(v___x_1280_, v___x_1284_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1287_ = lean_string_append(v___x_1285_, v___x_1286_);
v___x_1288_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1287_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
lean_dec(v_ty_1062_);
v___x_1289_ = lean_box(0);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1289_);
v___x_1291_ = v___x_1276_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_dec(v_ty_1062_);
return v___x_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1295_, lean_object* v_e_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_IR_Checker_checkExpr(v_ty_1295_, v_e_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1303_, lean_object* v_p_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_x_1310_; lean_object* v___x_1311_; 
v_x_1310_ = lean_ctor_get(v_p_1304_, 0);
lean_inc(v_x_1310_);
v___x_1311_ = l_Lean_IR_Checker_markIndex(v_x_1310_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1319_; 
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v___x_1311_, 0);
lean_dec(v_unused_1320_);
v___x_1313_ = v___x_1311_;
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v___x_1311_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = l_Lean_IR_LocalContext_addParam(v_ctx_1303_, v_p_1304_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1315_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_p_1304_);
lean_dec(v_ctx_1303_);
v_a_1321_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1311_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1329_, lean_object* v_p_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1329_, v_p_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1336_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_instMonadEIO___redArg();
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1339_ = l_StateRefT_x27_instMonad___redArg(v___x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1343_, lean_object* v_k_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v_toApplicative_1351_; lean_object* v_toFunctor_1352_; lean_object* v_toSeq_1353_; lean_object* v_toSeqLeft_1354_; lean_object* v_toSeqRight_1355_; lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_localCtx_1368_; lean_object* v_currentDecl_1369_; lean_object* v_decls_1370_; lean_object* v_a_1372_; lean_object* v___y_1376_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1350_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1351_ = lean_ctor_get(v___x_1350_, 0);
v_toFunctor_1352_ = lean_ctor_get(v_toApplicative_1351_, 0);
v_toSeq_1353_ = lean_ctor_get(v_toApplicative_1351_, 2);
v_toSeqLeft_1354_ = lean_ctor_get(v_toApplicative_1351_, 3);
v_toSeqRight_1355_ = lean_ctor_get(v_toApplicative_1351_, 4);
v___f_1356_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1357_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1352_, 2);
v___f_1358_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1358_, 0, v_toFunctor_1352_);
v___f_1359_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1359_, 0, v_toFunctor_1352_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___f_1358_);
lean_ctor_set(v___x_1360_, 1, v___f_1359_);
lean_inc(v_toSeqRight_1355_);
v___f_1361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1361_, 0, v_toSeqRight_1355_);
lean_inc(v_toSeqLeft_1354_);
v___f_1362_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1362_, 0, v_toSeqLeft_1354_);
lean_inc(v_toSeq_1353_);
v___f_1363_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1363_, 0, v_toSeq_1353_);
v___x_1364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1360_);
lean_ctor_set(v___x_1364_, 1, v___f_1356_);
lean_ctor_set(v___x_1364_, 2, v___f_1363_);
lean_ctor_set(v___x_1364_, 3, v___f_1362_);
lean_ctor_set(v___x_1364_, 4, v___f_1361_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___f_1357_);
v___x_1366_ = l_StateRefT_x27_instMonad___redArg(v___x_1365_);
v___x_1367_ = l_ReaderT_instMonad___redArg(v___x_1366_);
v_localCtx_1368_ = lean_ctor_get(v_a_1345_, 0);
v_currentDecl_1369_ = lean_ctor_get(v_a_1345_, 1);
v_decls_1370_ = lean_ctor_get(v_a_1345_, 2);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_array_get_size(v_ps_1343_);
v___x_1388_ = lean_nat_dec_lt(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v___x_1367_);
lean_dec_ref(v_ps_1343_);
lean_inc(v_localCtx_1368_);
v_a_1372_ = v_localCtx_1368_;
goto v___jp_1371_;
}
else
{
lean_object* v___f_1389_; uint8_t v___x_1390_; 
v___f_1389_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1390_ = lean_nat_dec_le(v___x_1387_, v___x_1387_);
if (v___x_1390_ == 0)
{
if (v___x_1388_ == 0)
{
lean_dec_ref(v___x_1367_);
lean_dec_ref(v_ps_1343_);
lean_inc(v_localCtx_1368_);
v_a_1372_ = v_localCtx_1368_;
goto v___jp_1371_;
}
else
{
size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1038__overap_1393_; lean_object* v___x_1394_; 
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = lean_usize_of_nat(v___x_1387_);
lean_inc(v_localCtx_1368_);
v___x_1038__overap_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1367_, v___f_1389_, v_ps_1343_, v___x_1391_, v___x_1392_, v_localCtx_1368_);
lean_inc(v_a_1348_);
lean_inc_ref(v_a_1347_);
lean_inc(v_a_1346_);
lean_inc_ref(v_a_1345_);
v___x_1394_ = lean_apply_5(v___x_1038__overap_1393_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, lean_box(0));
v___y_1376_ = v___x_1394_;
goto v___jp_1375_;
}
}
else
{
size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1042__overap_1397_; lean_object* v___x_1398_; 
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = lean_usize_of_nat(v___x_1387_);
lean_inc(v_localCtx_1368_);
v___x_1042__overap_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1367_, v___f_1389_, v_ps_1343_, v___x_1395_, v___x_1396_, v_localCtx_1368_);
lean_inc(v_a_1348_);
lean_inc_ref(v_a_1347_);
lean_inc(v_a_1346_);
lean_inc_ref(v_a_1345_);
v___x_1398_ = lean_apply_5(v___x_1042__overap_1397_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, lean_box(0));
v___y_1376_ = v___x_1398_;
goto v___jp_1375_;
}
}
v___jp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_inc_ref(v_decls_1370_);
lean_inc_ref(v_currentDecl_1369_);
v___x_1373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1372_);
lean_ctor_set(v___x_1373_, 1, v_currentDecl_1369_);
lean_ctor_set(v___x_1373_, 2, v_decls_1370_);
lean_inc(v_a_1348_);
lean_inc_ref(v_a_1347_);
lean_inc(v_a_1346_);
v___x_1374_ = lean_apply_5(v_k_1344_, v___x_1373_, v_a_1346_, v_a_1347_, v_a_1348_, lean_box(0));
return v___x_1374_;
}
v___jp_1375_:
{
if (lean_obj_tag(v___y_1376_) == 0)
{
lean_object* v_a_1377_; 
v_a_1377_ = lean_ctor_get(v___y_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___y_1376_, 1);
v_a_1372_ = v_a_1377_;
goto v___jp_1371_;
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v_k_1344_);
v_a_1378_ = lean_ctor_get(v___y_1376_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___y_1376_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___y_1376_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___y_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1399_, lean_object* v_k_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_IR_Checker_withParams(v_ps_1399_, v_k_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1407_, size_t v_i_1408_, size_t v_stop_1409_, lean_object* v_b_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_usize_dec_eq(v_i_1408_, v_stop_1409_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v_x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_array_uget_borrowed(v_as_1407_, v_i_1408_);
v_x_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_x_1418_);
v___x_1419_ = l_Lean_IR_Checker_markIndex(v_x_1418_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; 
lean_dec_ref_known(v___x_1419_, 1);
lean_inc(v___x_1417_);
v___x_1420_ = l_Lean_IR_LocalContext_addParam(v_b_1410_, v___x_1417_);
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1408_, v___x_1421_);
v_i_1408_ = v___x_1422_;
v_b_1410_ = v___x_1420_;
goto _start;
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_b_1410_);
v_a_1424_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1419_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1419_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_b_1410_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1433_, lean_object* v_i_1434_, lean_object* v_stop_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
size_t v_i_boxed_1442_; size_t v_stop_boxed_1443_; lean_object* v_res_1444_; 
v_i_boxed_1442_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_stop_boxed_1443_ = lean_unbox_usize(v_stop_1435_);
lean_dec(v_stop_1435_);
v_res_1444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1433_, v_i_boxed_1442_, v_stop_boxed_1443_, v_b_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v_as_1433_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_x_1452_; lean_object* v_b_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; 
switch(lean_obj_tag(v_fnBody_1445_))
{
case 0:
{
lean_object* v_x_1460_; lean_object* v_ty_1461_; lean_object* v_e_1462_; lean_object* v_b_1463_; lean_object* v___x_1464_; 
v_x_1460_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_x_1460_);
v_ty_1461_ = lean_ctor_get(v_fnBody_1445_, 1);
lean_inc_n(v_ty_1461_, 2);
v_e_1462_ = lean_ctor_get(v_fnBody_1445_, 2);
lean_inc_ref_n(v_e_1462_, 2);
v_b_1463_ = lean_ctor_get(v_fnBody_1445_, 3);
lean_inc(v_b_1463_);
lean_dec_ref_known(v_fnBody_1445_, 4);
v___x_1464_ = l_Lean_IR_Checker_checkExpr(v_ty_1461_, v_e_1462_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
lean_dec_ref_known(v___x_1464_, 1);
lean_inc(v_x_1460_);
v___x_1465_ = l_Lean_IR_Checker_markIndex(v_x_1460_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_localCtx_1466_; lean_object* v_currentDecl_1467_; lean_object* v_decls_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref_known(v___x_1465_, 1);
v_localCtx_1466_ = lean_ctor_get(v_a_1446_, 0);
lean_inc(v_localCtx_1466_);
v_currentDecl_1467_ = lean_ctor_get(v_a_1446_, 1);
lean_inc_ref(v_currentDecl_1467_);
v_decls_1468_ = lean_ctor_get(v_a_1446_, 2);
lean_inc_ref(v_decls_1468_);
lean_dec_ref(v_a_1446_);
v___x_1469_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1466_, v_x_1460_, v_ty_1461_, v_e_1462_);
v___x_1470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v_currentDecl_1467_);
lean_ctor_set(v___x_1470_, 2, v_decls_1468_);
v_fnBody_1445_ = v_b_1463_;
v_a_1446_ = v___x_1470_;
goto _start;
}
else
{
lean_dec(v_b_1463_);
lean_dec_ref(v_e_1462_);
lean_dec(v_ty_1461_);
lean_dec(v_x_1460_);
lean_dec_ref(v_a_1446_);
return v___x_1465_;
}
}
else
{
lean_dec(v_b_1463_);
lean_dec_ref(v_e_1462_);
lean_dec(v_ty_1461_);
lean_dec(v_x_1460_);
lean_dec_ref(v_a_1446_);
return v___x_1464_;
}
}
case 1:
{
lean_object* v_j_1472_; lean_object* v_xs_1473_; lean_object* v_v_1474_; lean_object* v_b_1475_; lean_object* v_a_1477_; lean_object* v___x_1486_; 
v_j_1472_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc_n(v_j_1472_, 2);
v_xs_1473_ = lean_ctor_get(v_fnBody_1445_, 1);
lean_inc_ref(v_xs_1473_);
v_v_1474_ = lean_ctor_get(v_fnBody_1445_, 2);
lean_inc(v_v_1474_);
v_b_1475_ = lean_ctor_get(v_fnBody_1445_, 3);
lean_inc(v_b_1475_);
lean_dec_ref_known(v_fnBody_1445_, 4);
v___x_1486_ = l_Lean_IR_Checker_markIndex(v_j_1472_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_localCtx_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
lean_dec_ref_known(v___x_1486_, 1);
v_localCtx_1487_ = lean_ctor_get(v_a_1446_, 0);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_array_get_size(v_xs_1473_);
v___x_1490_ = lean_nat_dec_lt(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_inc(v_localCtx_1487_);
v_a_1477_ = v_localCtx_1487_;
goto v___jp_1476_;
}
else
{
size_t v___x_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = lean_usize_of_nat(v___x_1489_);
lean_inc(v_localCtx_1487_);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1473_, v___x_1491_, v___x_1492_, v_localCtx_1487_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v_a_1477_ = v_a_1494_;
goto v___jp_1476_;
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_b_1475_);
lean_dec(v_v_1474_);
lean_dec_ref(v_xs_1473_);
lean_dec(v_j_1472_);
lean_dec_ref(v_a_1446_);
v_a_1495_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1493_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1493_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
else
{
lean_dec(v_b_1475_);
lean_dec(v_v_1474_);
lean_dec_ref(v_xs_1473_);
lean_dec(v_j_1472_);
lean_dec_ref(v_a_1446_);
return v___x_1486_;
}
v___jp_1476_:
{
lean_object* v_localCtx_1478_; lean_object* v_currentDecl_1479_; lean_object* v_decls_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_localCtx_1478_ = lean_ctor_get(v_a_1446_, 0);
lean_inc(v_localCtx_1478_);
v_currentDecl_1479_ = lean_ctor_get(v_a_1446_, 1);
lean_inc_ref_n(v_currentDecl_1479_, 2);
v_decls_1480_ = lean_ctor_get(v_a_1446_, 2);
lean_inc_ref_n(v_decls_1480_, 2);
lean_dec_ref(v_a_1446_);
v___x_1481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1481_, 0, v_a_1477_);
lean_ctor_set(v___x_1481_, 1, v_currentDecl_1479_);
lean_ctor_set(v___x_1481_, 2, v_decls_1480_);
lean_inc(v_v_1474_);
v___x_1482_ = l_Lean_IR_Checker_checkFnBody(v_v_1474_, v___x_1481_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref_known(v___x_1482_, 1);
v___x_1483_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1478_, v_j_1472_, v_xs_1473_, v_v_1474_);
v___x_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v_currentDecl_1479_);
lean_ctor_set(v___x_1484_, 2, v_decls_1480_);
v_fnBody_1445_ = v_b_1475_;
v_a_1446_ = v___x_1484_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1480_);
lean_dec_ref(v_currentDecl_1479_);
lean_dec(v_localCtx_1478_);
lean_dec(v_b_1475_);
lean_dec(v_v_1474_);
lean_dec_ref(v_xs_1473_);
lean_dec(v_j_1472_);
return v___x_1482_;
}
}
}
case 2:
{
lean_object* v_x_1503_; lean_object* v_y_1504_; lean_object* v_b_1505_; lean_object* v___x_1506_; 
v_x_1503_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_x_1503_);
v_y_1504_ = lean_ctor_get(v_fnBody_1445_, 2);
lean_inc(v_y_1504_);
v_b_1505_ = lean_ctor_get(v_fnBody_1445_, 3);
lean_inc(v_b_1505_);
lean_dec_ref_known(v_fnBody_1445_, 4);
v___x_1506_ = l_Lean_IR_Checker_checkVar(v_x_1503_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v___x_1507_; 
lean_dec_ref_known(v___x_1506_, 1);
v___x_1507_ = l_Lean_IR_Checker_checkArg(v_y_1504_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_dec_ref_known(v___x_1507_, 1);
v_fnBody_1445_ = v_b_1505_;
goto _start;
}
else
{
lean_dec(v_b_1505_);
lean_dec_ref(v_a_1446_);
return v___x_1507_;
}
}
else
{
lean_dec(v_b_1505_);
lean_dec(v_y_1504_);
lean_dec_ref(v_a_1446_);
return v___x_1506_;
}
}
case 3:
{
lean_object* v_x_1509_; lean_object* v_b_1510_; lean_object* v___x_1511_; 
v_x_1509_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_x_1509_);
v_b_1510_ = lean_ctor_get(v_fnBody_1445_, 2);
lean_inc(v_b_1510_);
lean_dec_ref_known(v_fnBody_1445_, 3);
v___x_1511_ = l_Lean_IR_Checker_checkVar(v_x_1509_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_dec_ref_known(v___x_1511_, 1);
v_fnBody_1445_ = v_b_1510_;
goto _start;
}
else
{
lean_dec(v_b_1510_);
lean_dec_ref(v_a_1446_);
return v___x_1511_;
}
}
case 4:
{
lean_object* v_x_1513_; lean_object* v_y_1514_; lean_object* v_b_1515_; lean_object* v___x_1516_; 
v_x_1513_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_x_1513_);
v_y_1514_ = lean_ctor_get(v_fnBody_1445_, 2);
lean_inc(v_y_1514_);
v_b_1515_ = lean_ctor_get(v_fnBody_1445_, 3);
lean_inc(v_b_1515_);
lean_dec_ref_known(v_fnBody_1445_, 4);
v___x_1516_ = l_Lean_IR_Checker_checkVar(v_x_1513_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref_known(v___x_1516_, 1);
v___x_1517_ = l_Lean_IR_Checker_checkVar(v_y_1514_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_dec_ref_known(v___x_1517_, 1);
v_fnBody_1445_ = v_b_1515_;
goto _start;
}
else
{
lean_dec(v_b_1515_);
lean_dec_ref(v_a_1446_);
return v___x_1517_;
}
}
else
{
lean_dec(v_b_1515_);
lean_dec(v_y_1514_);
lean_dec_ref(v_a_1446_);
return v___x_1516_;
}
}
case 5:
{
lean_object* v_x_1519_; lean_object* v_y_1520_; lean_object* v_b_1521_; lean_object* v___x_1522_; 
v_x_1519_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_x_1519_);
v_y_1520_ = lean_ctor_get(v_fnBody_1445_, 3);
lean_inc(v_y_1520_);
v_b_1521_ = lean_ctor_get(v_fnBody_1445_, 5);
lean_inc(v_b_1521_);
lean_dec_ref_known(v_fnBody_1445_, 6);
v___x_1522_ = l_Lean_IR_Checker_checkVar(v_x_1519_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1523_; 
lean_dec_ref_known(v___x_1522_, 1);
v___x_1523_ = l_Lean_IR_Checker_checkVar(v_y_1520_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_dec_ref_known(v___x_1523_, 1);
v_fnBody_1445_ = v_b_1521_;
goto _start;
}
else
{
lean_dec(v_b_1521_);
lean_dec_ref(v_a_1446_);
return v___x_1523_;
}
}
else
{
lean_dec(v_b_1521_);
lean_dec(v_y_1520_);
lean_dec_ref(v_a_1446_);
return v___x_1522_;
}
}
case 8:
{
lean_object* v_x_1525_; lean_object* v_b_1526_; lean_object* v___x_1527_; 
v_x_1525_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_x_1525_);
v_b_1526_ = lean_ctor_get(v_fnBody_1445_, 1);
lean_inc(v_b_1526_);
lean_dec_ref_known(v_fnBody_1445_, 2);
v___x_1527_ = l_Lean_IR_Checker_checkVar(v_x_1525_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_dec_ref_known(v___x_1527_, 1);
v_fnBody_1445_ = v_b_1526_;
goto _start;
}
else
{
lean_dec(v_b_1526_);
lean_dec_ref(v_a_1446_);
return v___x_1527_;
}
}
case 9:
{
lean_object* v_x_1529_; lean_object* v_cs_1530_; lean_object* v___x_1531_; 
v_x_1529_ = lean_ctor_get(v_fnBody_1445_, 1);
lean_inc(v_x_1529_);
v_cs_1530_ = lean_ctor_get(v_fnBody_1445_, 3);
lean_inc_ref(v_cs_1530_);
lean_dec_ref_known(v_fnBody_1445_, 4);
v___x_1531_ = l_Lean_IR_Checker_checkVar(v_x_1529_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1552_; 
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; 
v_unused_1553_ = lean_ctor_get(v___x_1531_, 0);
lean_dec(v_unused_1553_);
v___x_1533_ = v___x_1531_;
v_isShared_1534_ = v_isSharedCheck_1552_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v___x_1531_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1552_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_array_get_size(v_cs_1530_);
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_nat_dec_lt(v___x_1535_, v___x_1536_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref(v_cs_1530_);
lean_dec_ref(v_a_1446_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1537_);
v___x_1540_ = v___x_1533_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1537_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
else
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_nat_dec_le(v___x_1536_, v___x_1536_);
if (v___x_1542_ == 0)
{
if (v___x_1538_ == 0)
{
lean_object* v___x_1544_; 
lean_dec_ref(v_cs_1530_);
lean_dec_ref(v_a_1446_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1537_);
v___x_1544_ = v___x_1533_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1537_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
else
{
size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
lean_del_object(v___x_1533_);
v___x_1546_ = ((size_t)0ULL);
v___x_1547_ = lean_usize_of_nat(v___x_1536_);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1530_, v___x_1546_, v___x_1547_, v___x_1537_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec_ref(v_a_1446_);
lean_dec_ref(v_cs_1530_);
return v___x_1548_;
}
}
else
{
size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
lean_del_object(v___x_1533_);
v___x_1549_ = ((size_t)0ULL);
v___x_1550_ = lean_usize_of_nat(v___x_1536_);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1530_, v___x_1549_, v___x_1550_, v___x_1537_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec_ref(v_a_1446_);
lean_dec_ref(v_cs_1530_);
return v___x_1551_;
}
}
}
}
else
{
lean_dec_ref(v_cs_1530_);
lean_dec_ref(v_a_1446_);
return v___x_1531_;
}
}
case 10:
{
lean_object* v_x_1554_; lean_object* v___x_1555_; 
v_x_1554_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_x_1554_);
lean_dec_ref_known(v_fnBody_1445_, 1);
v___x_1555_ = l_Lean_IR_Checker_checkArg(v_x_1554_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec_ref(v_a_1446_);
return v___x_1555_;
}
case 11:
{
lean_object* v_j_1556_; lean_object* v_ys_1557_; lean_object* v___x_1558_; 
v_j_1556_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_j_1556_);
v_ys_1557_ = lean_ctor_get(v_fnBody_1445_, 1);
lean_inc_ref(v_ys_1557_);
lean_dec_ref_known(v_fnBody_1445_, 2);
v___x_1558_ = l_Lean_IR_Checker_checkJP(v_j_1556_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; 
lean_dec_ref_known(v___x_1558_, 1);
v___x_1559_ = l_Lean_IR_Checker_checkArgs(v_ys_1557_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec_ref(v_a_1446_);
lean_dec_ref(v_ys_1557_);
return v___x_1559_;
}
else
{
lean_dec_ref(v_ys_1557_);
lean_dec_ref(v_a_1446_);
return v___x_1558_;
}
}
case 12:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec_ref(v_a_1446_);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
default: 
{
lean_object* v_x_1562_; lean_object* v_b_1563_; 
v_x_1562_ = lean_ctor_get(v_fnBody_1445_, 0);
lean_inc(v_x_1562_);
v_b_1563_ = lean_ctor_get(v_fnBody_1445_, 2);
lean_inc(v_b_1563_);
lean_dec(v_fnBody_1445_);
v_x_1452_ = v_x_1562_;
v_b_1453_ = v_b_1563_;
v___y_1454_ = v_a_1446_;
v___y_1455_ = v_a_1447_;
v___y_1456_ = v_a_1448_;
v___y_1457_ = v_a_1449_;
goto v___jp_1451_;
}
}
v___jp_1451_:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_IR_Checker_checkVar(v_x_1452_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_dec_ref_known(v___x_1458_, 1);
v_fnBody_1445_ = v_b_1453_;
v_a_1446_ = v___y_1454_;
v_a_1447_ = v___y_1455_;
v_a_1448_ = v___y_1456_;
v_a_1449_ = v___y_1457_;
goto _start;
}
else
{
lean_dec_ref(v___y_1454_);
lean_dec(v_b_1453_);
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1564_, size_t v_i_1565_, size_t v_stop_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_usize_dec_eq(v_i_1565_, v_stop_1566_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_array_uget_borrowed(v_as_1564_, v_i_1565_);
v___x_1575_ = l_Lean_IR_Alt_body(v___x_1574_);
lean_inc_ref(v___y_1568_);
v___x_1576_ = l_Lean_IR_Checker_checkFnBody(v___x_1575_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; size_t v___x_1578_; size_t v___x_1579_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = ((size_t)1ULL);
v___x_1579_ = lean_usize_add(v_i_1565_, v___x_1578_);
v_i_1565_ = v___x_1579_;
v_b_1567_ = v_a_1577_;
goto _start;
}
else
{
return v___x_1576_;
}
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_b_1567_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1582_, lean_object* v_i_1583_, lean_object* v_stop_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
size_t v_i_boxed_1591_; size_t v_stop_boxed_1592_; lean_object* v_res_1593_; 
v_i_boxed_1591_ = lean_unbox_usize(v_i_1583_);
lean_dec(v_i_1583_);
v_stop_boxed_1592_ = lean_unbox_usize(v_stop_1584_);
lean_dec(v_stop_1584_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1582_, v_i_boxed_1591_, v_stop_boxed_1592_, v_b_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec_ref(v_as_1582_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
if (lean_obj_tag(v_x_1601_) == 0)
{
lean_object* v_xs_1607_; lean_object* v_body_1608_; lean_object* v_localCtx_1609_; lean_object* v_currentDecl_1610_; lean_object* v_decls_1611_; lean_object* v_a_1613_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_xs_1607_ = lean_ctor_get(v_x_1601_, 1);
lean_inc_ref(v_xs_1607_);
v_body_1608_ = lean_ctor_get(v_x_1601_, 3);
lean_inc(v_body_1608_);
lean_dec_ref_known(v_x_1601_, 5);
v_localCtx_1609_ = lean_ctor_get(v_a_1602_, 0);
v_currentDecl_1610_ = lean_ctor_get(v_a_1602_, 1);
v_decls_1611_ = lean_ctor_get(v_a_1602_, 2);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_array_get_size(v_xs_1607_);
v___x_1618_ = lean_nat_dec_lt(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_dec_ref(v_xs_1607_);
lean_inc(v_localCtx_1609_);
v_a_1613_ = v_localCtx_1609_;
goto v___jp_1612_;
}
else
{
size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = ((size_t)0ULL);
v___x_1620_ = lean_usize_of_nat(v___x_1617_);
lean_inc(v_localCtx_1609_);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1607_, v___x_1619_, v___x_1620_, v_localCtx_1609_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec_ref(v_xs_1607_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v_a_1613_ = v_a_1622_;
goto v___jp_1612_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_body_1608_);
v_a_1623_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1621_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
v___jp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_inc_ref(v_decls_1611_);
lean_inc_ref(v_currentDecl_1610_);
v___x_1614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1614_, 0, v_a_1613_);
lean_ctor_set(v___x_1614_, 1, v_currentDecl_1610_);
lean_ctor_set(v___x_1614_, 2, v_decls_1611_);
v___x_1615_ = l_Lean_IR_Checker_checkFnBody(v_body_1608_, v___x_1614_, v_a_1603_, v_a_1604_, v_a_1605_);
return v___x_1615_;
}
}
else
{
lean_object* v_xs_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_xs_1631_ = lean_ctor_get(v_x_1601_, 1);
lean_inc_ref(v_xs_1631_);
lean_dec_ref_known(v_x_1601_, 4);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = lean_array_get_size(v_xs_1631_);
v___x_1635_ = lean_nat_dec_lt(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref(v_xs_1631_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1632_);
return v___x_1636_;
}
else
{
lean_object* v_localCtx_1637_; size_t v___x_1638_; size_t v___x_1639_; lean_object* v___x_1640_; 
v_localCtx_1637_ = lean_ctor_get(v_a_1602_, 0);
v___x_1638_ = ((size_t)0ULL);
v___x_1639_ = lean_usize_of_nat(v___x_1634_);
lean_inc(v_localCtx_1637_);
v___x_1640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1631_, v___x_1638_, v___x_1639_, v_localCtx_1637_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec_ref(v_xs_1631_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v___x_1640_, 0);
lean_dec(v_unused_1648_);
v___x_1642_ = v___x_1640_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_dec(v___x_1640_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1632_);
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1632_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_a_1649_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1640_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1640_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_IR_Checker_checkDecl(v_x_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_1664_, lean_object* v_decl_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1669_ = lean_box(1);
lean_inc_ref(v_decl_1665_);
v___x_1670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_decl_1665_);
lean_ctor_set(v___x_1670_, 2, v_decls_1664_);
v___x_1671_ = lean_st_mk_ref(v___x_1669_);
v___x_1672_ = l_Lean_IR_Checker_checkDecl(v_decl_1665_, v___x_1670_, v___x_1671_, v_a_1666_, v_a_1667_);
lean_dec_ref_known(v___x_1670_, 3);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_st_ref_get(v___x_1671_);
lean_dec(v___x_1671_);
lean_dec(v___x_1677_);
if (v_isShared_1676_ == 0)
{
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1673_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_dec(v___x_1671_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* v_decls_1682_, lean_object* v_decl_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_IR_checkDecl(v_decls_1682_, v_decl_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* v_decls_1688_, lean_object* v_as_1689_, size_t v_i_1690_, size_t v_stop_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_usize_dec_eq(v_i_1690_, v_stop_1691_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_array_uget_borrowed(v_as_1689_, v_i_1690_);
lean_inc(v___x_1697_);
lean_inc_ref(v_decls_1688_);
v___x_1698_ = l_Lean_IR_checkDecl(v_decls_1688_, v___x_1697_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; size_t v___x_1700_; size_t v___x_1701_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_i_1690_, v___x_1700_);
v_i_1690_ = v___x_1701_;
v_b_1692_ = v_a_1699_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1688_);
return v___x_1698_;
}
}
else
{
lean_object* v___x_1703_; 
lean_dec_ref(v_decls_1688_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_b_1692_);
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* v_decls_1704_, lean_object* v_as_1705_, lean_object* v_i_1706_, lean_object* v_stop_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
size_t v_i_boxed_1712_; size_t v_stop_boxed_1713_; lean_object* v_res_1714_; 
v_i_boxed_1712_ = lean_unbox_usize(v_i_1706_);
lean_dec(v_i_1706_);
v_stop_boxed_1713_ = lean_unbox_usize(v_stop_1707_);
lean_dec(v_stop_1707_);
v_res_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1704_, v_as_1705_, v_i_boxed_1712_, v_stop_boxed_1713_, v_b_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec_ref(v_as_1705_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* v_decls_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_array_get_size(v_decls_1715_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_nat_dec_lt(v___x_1719_, v___x_1720_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; 
lean_dec_ref(v_decls_1715_);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
return v___x_1723_;
}
else
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_nat_dec_le(v___x_1720_, v___x_1720_);
if (v___x_1724_ == 0)
{
if (v___x_1722_ == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref(v_decls_1715_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1721_);
return v___x_1725_;
}
else
{
size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = ((size_t)0ULL);
v___x_1727_ = lean_usize_of_nat(v___x_1720_);
lean_inc_ref(v_decls_1715_);
v___x_1728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1715_, v_decls_1715_, v___x_1726_, v___x_1727_, v___x_1721_, v_a_1716_, v_a_1717_);
lean_dec_ref(v_decls_1715_);
return v___x_1728_;
}
}
else
{
size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = lean_usize_of_nat(v___x_1720_);
lean_inc_ref(v_decls_1715_);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1715_, v_decls_1715_, v___x_1729_, v___x_1730_, v___x_1721_, v_a_1716_, v_a_1717_);
lean_dec_ref(v_decls_1715_);
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_IR_checkDecls(v_decls_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
return v_res_1736_;
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
