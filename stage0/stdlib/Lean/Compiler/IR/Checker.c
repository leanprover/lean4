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
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
lean_ctor_set(v___x_6_, 4, v___x_4_);
lean_ctor_set(v___x_6_, 5, v___x_4_);
lean_ctor_set(v___x_6_, 6, v___x_4_);
lean_ctor_set(v___x_6_, 7, v___x_4_);
lean_ctor_set(v___x_6_, 8, v___x_4_);
lean_ctor_set(v___x_6_, 9, v___x_4_);
lean_ctor_set(v___x_6_, 10, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(32u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = ((size_t)5ULL);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_unsigned_to_nat(32u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3);
v___x_15_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_11_);
lean_ctor_set(v___x_15_, 3, v___x_11_);
lean_ctor_set_usize(v___x_15_, 4, v___x_10_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_box(1);
v___x_17_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v_toCold_25_; lean_object* v_env_26_; lean_object* v_options_27_; uint8_t v___x_28_; lean_object* v_env_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_toCold_25_ = lean_ctor_get(v___y_21_, 0);
v_env_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_24_);
v_options_27_ = lean_ctor_get(v_toCold_25_, 2);
v___x_28_ = 0;
v_env_29_ = l_Lean_Environment_setRecordingDeps(v_env_26_, v___x_28_);
v___x_30_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2);
v___x_31_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_27_);
v___x_32_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_32_, 0, v_env_29_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
lean_ctor_set(v___x_32_, 2, v___x_31_);
lean_ctor_set(v___x_32_, 3, v_options_27_);
v___x_33_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_msgData_20_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msgData_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_ref_44_; lean_object* v___x_45_; lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
v_ref_44_ = lean_ctor_get(v___y_41_, 2);
v___x_45_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msg_40_, v___y_41_, v___y_42_);
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_54_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
lean_inc(v_ref_44_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v_ref_44_);
lean_ctor_set(v___x_50_, 1, v_a_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 1);
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object* v_msg_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_59_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0));
v___x_62_ = l_Lean_stringToMessageData(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__2));
v___x_65_ = l_Lean_stringToMessageData(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object* v_msg_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_currentDecl_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_currentDecl_72_ = lean_ctor_get(v_a_67_, 1);
v___x_73_ = l_Lean_IR_Decl_name(v_currentDecl_72_);
v___x_74_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__1, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1);
v___x_75_ = 0;
v___x_76_ = l_Lean_MessageData_ofConstName(v___x_73_, v___x_75_);
v___x_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_74_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__3, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3);
v___x_79_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = l_Lean_stringToMessageData(v_msg_66_);
v___x_81_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v___x_81_, v_a_69_, v_a_70_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object* v_msg_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object* v_00_u03b1_90_, lean_object* v_msg_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object* v_00_u03b1_98_, lean_object* v_msg_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_IR_Checker_throwCheckerError(v_00_u03b1_98_, v_msg_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object* v_00_u03b1_106_, lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_107_, v___y_110_, v___y_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object* v_00_u03b1_114_, lean_object* v_msg_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(v_00_u03b1_114_, v_msg_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object* v_k_122_, lean_object* v_v_123_, lean_object* v_t_124_){
_start:
{
if (lean_obj_tag(v_t_124_) == 0)
{
lean_object* v_size_125_; lean_object* v_k_126_; lean_object* v_v_127_; lean_object* v_l_128_; lean_object* v_r_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_410_; 
v_size_125_ = lean_ctor_get(v_t_124_, 0);
v_k_126_ = lean_ctor_get(v_t_124_, 1);
v_v_127_ = lean_ctor_get(v_t_124_, 2);
v_l_128_ = lean_ctor_get(v_t_124_, 3);
v_r_129_ = lean_ctor_get(v_t_124_, 4);
v_isSharedCheck_410_ = !lean_is_exclusive(v_t_124_);
if (v_isSharedCheck_410_ == 0)
{
v___x_131_ = v_t_124_;
v_isShared_132_ = v_isSharedCheck_410_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_r_129_);
lean_inc(v_l_128_);
lean_inc(v_v_127_);
lean_inc(v_k_126_);
lean_inc(v_size_125_);
lean_dec(v_t_124_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_410_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
uint8_t v___x_133_; 
v___x_133_ = lean_nat_dec_lt(v_k_122_, v_k_126_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_eq(v_k_122_, v_k_126_);
if (v___x_134_ == 0)
{
lean_object* v_impl_135_; lean_object* v___x_136_; 
lean_dec(v_size_125_);
v_impl_135_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_122_, v_v_123_, v_r_129_);
v___x_136_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_128_) == 0)
{
lean_object* v_size_137_; lean_object* v_size_138_; lean_object* v_k_139_; lean_object* v_v_140_; lean_object* v_l_141_; lean_object* v_r_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_size_137_ = lean_ctor_get(v_l_128_, 0);
v_size_138_ = lean_ctor_get(v_impl_135_, 0);
v_k_139_ = lean_ctor_get(v_impl_135_, 1);
v_v_140_ = lean_ctor_get(v_impl_135_, 2);
v_l_141_ = lean_ctor_get(v_impl_135_, 3);
lean_inc(v_l_141_);
v_r_142_ = lean_ctor_get(v_impl_135_, 4);
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_mul(v___x_143_, v_size_137_);
v___x_145_ = lean_nat_dec_lt(v___x_144_, v_size_138_);
lean_dec(v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v_l_141_);
v___x_146_ = lean_nat_add(v___x_136_, v_size_137_);
v___x_147_ = lean_nat_add(v___x_146_, v_size_138_);
lean_dec(v___x_146_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v_impl_135_);
lean_ctor_set(v___x_131_, 0, v___x_147_);
v___x_149_ = v___x_131_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_l_128_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_impl_135_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_214_; 
lean_inc(v_r_142_);
lean_inc(v_v_140_);
lean_inc(v_k_139_);
lean_inc(v_size_138_);
v_isSharedCheck_214_ = !lean_is_exclusive(v_impl_135_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; lean_object* v_unused_216_; lean_object* v_unused_217_; lean_object* v_unused_218_; lean_object* v_unused_219_; 
v_unused_215_ = lean_ctor_get(v_impl_135_, 4);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_impl_135_, 3);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_impl_135_, 2);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_impl_135_, 1);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_impl_135_, 0);
lean_dec(v_unused_219_);
v___x_152_ = v_impl_135_;
v_isShared_153_ = v_isSharedCheck_214_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_impl_135_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_214_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_size_154_; lean_object* v_k_155_; lean_object* v_v_156_; lean_object* v_l_157_; lean_object* v_r_158_; lean_object* v_size_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_size_154_ = lean_ctor_get(v_l_141_, 0);
v_k_155_ = lean_ctor_get(v_l_141_, 1);
v_v_156_ = lean_ctor_get(v_l_141_, 2);
v_l_157_ = lean_ctor_get(v_l_141_, 3);
v_r_158_ = lean_ctor_get(v_l_141_, 4);
v_size_159_ = lean_ctor_get(v_r_142_, 0);
v___x_160_ = lean_unsigned_to_nat(2u);
v___x_161_ = lean_nat_mul(v___x_160_, v_size_159_);
v___x_162_ = lean_nat_dec_lt(v_size_154_, v___x_161_);
lean_dec(v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_190_; 
lean_inc(v_r_158_);
lean_inc(v_l_157_);
lean_inc(v_v_156_);
lean_inc(v_k_155_);
v_isSharedCheck_190_ = !lean_is_exclusive(v_l_141_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; lean_object* v_unused_195_; 
v_unused_191_ = lean_ctor_get(v_l_141_, 4);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_l_141_, 3);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_l_141_, 2);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_l_141_, 1);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_l_141_, 0);
lean_dec(v_unused_195_);
v___x_164_ = v_l_141_;
v_isShared_165_ = v_isSharedCheck_190_;
goto v_resetjp_163_;
}
else
{
lean_dec(v_l_141_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_190_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_180_; 
v___x_166_ = lean_nat_add(v___x_136_, v_size_137_);
v___x_167_ = lean_nat_add(v___x_166_, v_size_138_);
lean_dec(v_size_138_);
if (lean_obj_tag(v_l_157_) == 0)
{
lean_object* v_size_188_; 
v_size_188_ = lean_ctor_get(v_l_157_, 0);
lean_inc(v_size_188_);
v___y_180_ = v_size_188_;
goto v___jp_179_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___y_180_ = v___x_189_;
goto v___jp_179_;
}
v___jp_168_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_nat_add(v___y_169_, v___y_171_);
lean_dec(v___y_171_);
lean_dec(v___y_169_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 4, v_r_142_);
lean_ctor_set(v___x_164_, 3, v_r_158_);
lean_ctor_set(v___x_164_, 2, v_v_140_);
lean_ctor_set(v___x_164_, 1, v_k_139_);
lean_ctor_set(v___x_164_, 0, v___x_172_);
v___x_174_ = v___x_164_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_k_139_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_v_140_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_r_158_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v_r_142_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v___x_174_);
lean_ctor_set(v___x_152_, 3, v___y_170_);
lean_ctor_set(v___x_152_, 2, v_v_156_);
lean_ctor_set(v___x_152_, 1, v_k_155_);
lean_ctor_set(v___x_152_, 0, v___x_167_);
v___x_176_ = v___x_152_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_k_155_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_v_156_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v___y_170_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
v___jp_179_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = lean_nat_add(v___x_166_, v___y_180_);
lean_dec(v___y_180_);
lean_dec(v___x_166_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v_l_157_);
lean_ctor_set(v___x_131_, 0, v___x_181_);
v___x_183_ = v___x_131_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_l_128_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v_l_157_);
v___x_183_ = v_reuseFailAlloc_187_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; 
v___x_184_ = lean_nat_add(v___x_136_, v_size_159_);
if (lean_obj_tag(v_r_158_) == 0)
{
lean_object* v_size_185_; 
v_size_185_ = lean_ctor_get(v_r_158_, 0);
lean_inc(v_size_185_);
v___y_169_ = v___x_184_;
v___y_170_ = v___x_183_;
v___y_171_ = v_size_185_;
goto v___jp_168_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___y_169_ = v___x_184_;
v___y_170_ = v___x_183_;
v___y_171_ = v___x_186_;
goto v___jp_168_;
}
}
}
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
lean_del_object(v___x_131_);
v___x_196_ = lean_nat_add(v___x_136_, v_size_137_);
v___x_197_ = lean_nat_add(v___x_196_, v_size_138_);
lean_dec(v_size_138_);
v___x_198_ = lean_nat_add(v___x_196_, v_size_154_);
lean_dec(v___x_196_);
lean_inc_ref(v_l_128_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v_l_141_);
lean_ctor_set(v___x_152_, 3, v_l_128_);
lean_ctor_set(v___x_152_, 2, v_v_127_);
lean_ctor_set(v___x_152_, 1, v_k_126_);
lean_ctor_set(v___x_152_, 0, v___x_198_);
v___x_200_ = v___x_152_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v_l_128_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v_l_141_);
v___x_200_ = v_reuseFailAlloc_213_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_isSharedCheck_207_ = !lean_is_exclusive(v_l_128_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; 
v_unused_208_ = lean_ctor_get(v_l_128_, 4);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_l_128_, 3);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_l_128_, 2);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_l_128_, 1);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_l_128_, 0);
lean_dec(v_unused_212_);
v___x_202_ = v_l_128_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_l_128_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 4, v_r_142_);
lean_ctor_set(v___x_202_, 3, v___x_200_);
lean_ctor_set(v___x_202_, 2, v_v_140_);
lean_ctor_set(v___x_202_, 1, v_k_139_);
lean_ctor_set(v___x_202_, 0, v___x_197_);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_k_139_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_v_140_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_r_142_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_220_; 
v_l_220_ = lean_ctor_get(v_impl_135_, 3);
lean_inc(v_l_220_);
if (lean_obj_tag(v_l_220_) == 0)
{
lean_object* v_r_221_; lean_object* v_k_222_; lean_object* v_v_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_246_; 
v_r_221_ = lean_ctor_get(v_impl_135_, 4);
v_k_222_ = lean_ctor_get(v_impl_135_, 1);
v_v_223_ = lean_ctor_get(v_impl_135_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_impl_135_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; 
v_unused_247_ = lean_ctor_get(v_impl_135_, 3);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_impl_135_, 0);
lean_dec(v_unused_248_);
v___x_225_ = v_impl_135_;
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_r_221_);
lean_inc(v_v_223_);
lean_inc(v_k_222_);
lean_dec(v_impl_135_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_k_227_; lean_object* v_v_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_242_; 
v_k_227_ = lean_ctor_get(v_l_220_, 1);
v_v_228_ = lean_ctor_get(v_l_220_, 2);
v_isSharedCheck_242_ = !lean_is_exclusive(v_l_220_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; lean_object* v_unused_244_; lean_object* v_unused_245_; 
v_unused_243_ = lean_ctor_get(v_l_220_, 4);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_l_220_, 3);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_l_220_, 0);
lean_dec(v_unused_245_);
v___x_230_ = v_l_220_;
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_v_228_);
lean_inc(v_k_227_);
lean_dec(v_l_220_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_221_, 2);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 4, v_r_221_);
lean_ctor_set(v___x_230_, 3, v_r_221_);
lean_ctor_set(v___x_230_, 2, v_v_127_);
lean_ctor_set(v___x_230_, 1, v_k_126_);
lean_ctor_set(v___x_230_, 0, v___x_136_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_r_221_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_r_221_);
v___x_234_ = v_reuseFailAlloc_241_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
lean_inc(v_r_221_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 3, v_r_221_);
lean_ctor_set(v___x_225_, 0, v___x_136_);
v___x_236_ = v___x_225_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_k_222_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_v_223_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_r_221_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_r_221_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v___x_236_);
lean_ctor_set(v___x_131_, 3, v___x_234_);
lean_ctor_set(v___x_131_, 2, v_v_228_);
lean_ctor_set(v___x_131_, 1, v_k_227_);
lean_ctor_set(v___x_131_, 0, v___x_232_);
v___x_238_ = v___x_131_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_k_227_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_v_228_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
else
{
lean_object* v_r_249_; 
v_r_249_ = lean_ctor_get(v_impl_135_, 4);
lean_inc(v_r_249_);
if (lean_obj_tag(v_r_249_) == 0)
{
lean_object* v_k_250_; lean_object* v_v_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_262_; 
v_k_250_ = lean_ctor_get(v_impl_135_, 1);
v_v_251_ = lean_ctor_get(v_impl_135_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v_impl_135_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; lean_object* v_unused_264_; lean_object* v_unused_265_; 
v_unused_263_ = lean_ctor_get(v_impl_135_, 4);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_impl_135_, 3);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_impl_135_, 0);
lean_dec(v_unused_265_);
v___x_253_ = v_impl_135_;
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_v_251_);
lean_inc(v_k_250_);
lean_dec(v_impl_135_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(3u);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 4, v_l_220_);
lean_ctor_set(v___x_253_, 2, v_v_127_);
lean_ctor_set(v___x_253_, 1, v_k_126_);
lean_ctor_set(v___x_253_, 0, v___x_136_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_l_220_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_l_220_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v_r_249_);
lean_ctor_set(v___x_131_, 3, v___x_257_);
lean_ctor_set(v___x_131_, 2, v_v_251_);
lean_ctor_set(v___x_131_, 1, v_k_250_);
lean_ctor_set(v___x_131_, 0, v___x_255_);
v___x_259_ = v___x_131_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_k_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_v_251_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_r_249_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_unsigned_to_nat(2u);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v_impl_135_);
lean_ctor_set(v___x_131_, 3, v_r_249_);
lean_ctor_set(v___x_131_, 0, v___x_266_);
v___x_268_ = v___x_131_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_r_249_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_impl_135_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
else
{
lean_object* v___x_271_; 
lean_dec(v_v_127_);
lean_dec(v_k_126_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 2, v_v_123_);
lean_ctor_set(v___x_131_, 1, v_k_122_);
v___x_271_ = v___x_131_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_size_125_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_l_128_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v_r_129_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_impl_273_; lean_object* v___x_274_; 
lean_dec(v_size_125_);
v_impl_273_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_122_, v_v_123_, v_l_128_);
v___x_274_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_129_) == 0)
{
lean_object* v_size_275_; lean_object* v_size_276_; lean_object* v_k_277_; lean_object* v_v_278_; lean_object* v_l_279_; lean_object* v_r_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_size_275_ = lean_ctor_get(v_r_129_, 0);
v_size_276_ = lean_ctor_get(v_impl_273_, 0);
v_k_277_ = lean_ctor_get(v_impl_273_, 1);
v_v_278_ = lean_ctor_get(v_impl_273_, 2);
v_l_279_ = lean_ctor_get(v_impl_273_, 3);
v_r_280_ = lean_ctor_get(v_impl_273_, 4);
lean_inc(v_r_280_);
v___x_281_ = lean_unsigned_to_nat(3u);
v___x_282_ = lean_nat_mul(v___x_281_, v_size_275_);
v___x_283_ = lean_nat_dec_lt(v___x_282_, v_size_276_);
lean_dec(v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_dec(v_r_280_);
v___x_284_ = lean_nat_add(v___x_274_, v_size_276_);
v___x_285_ = lean_nat_add(v___x_284_, v_size_275_);
lean_dec(v___x_284_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 3, v_impl_273_);
lean_ctor_set(v___x_131_, 0, v___x_285_);
v___x_287_ = v___x_131_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_impl_273_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_r_129_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_354_; 
lean_inc(v_l_279_);
lean_inc(v_v_278_);
lean_inc(v_k_277_);
lean_inc(v_size_276_);
v_isSharedCheck_354_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; lean_object* v_unused_358_; lean_object* v_unused_359_; 
v_unused_355_ = lean_ctor_get(v_impl_273_, 4);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_impl_273_, 2);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_impl_273_, 1);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_359_);
v___x_290_ = v_impl_273_;
v_isShared_291_ = v_isSharedCheck_354_;
goto v_resetjp_289_;
}
else
{
lean_dec(v_impl_273_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_354_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_size_292_; lean_object* v_size_293_; lean_object* v_k_294_; lean_object* v_v_295_; lean_object* v_l_296_; lean_object* v_r_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_size_292_ = lean_ctor_get(v_l_279_, 0);
v_size_293_ = lean_ctor_get(v_r_280_, 0);
v_k_294_ = lean_ctor_get(v_r_280_, 1);
v_v_295_ = lean_ctor_get(v_r_280_, 2);
v_l_296_ = lean_ctor_get(v_r_280_, 3);
v_r_297_ = lean_ctor_get(v_r_280_, 4);
v___x_298_ = lean_unsigned_to_nat(2u);
v___x_299_ = lean_nat_mul(v___x_298_, v_size_292_);
v___x_300_ = lean_nat_dec_lt(v_size_293_, v___x_299_);
lean_dec(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_329_; 
lean_inc(v_r_297_);
lean_inc(v_l_296_);
lean_inc(v_v_295_);
lean_inc(v_k_294_);
v_isSharedCheck_329_ = !lean_is_exclusive(v_r_280_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; lean_object* v_unused_331_; lean_object* v_unused_332_; lean_object* v_unused_333_; lean_object* v_unused_334_; 
v_unused_330_ = lean_ctor_get(v_r_280_, 4);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_r_280_, 3);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_r_280_, 2);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_r_280_, 1);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_r_280_, 0);
lean_dec(v_unused_334_);
v___x_302_ = v_r_280_;
v_isShared_303_ = v_isSharedCheck_329_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_r_280_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_329_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___x_317_; lean_object* v___y_319_; 
v___x_304_ = lean_nat_add(v___x_274_, v_size_276_);
lean_dec(v_size_276_);
v___x_305_ = lean_nat_add(v___x_304_, v_size_275_);
lean_dec(v___x_304_);
v___x_317_ = lean_nat_add(v___x_274_, v_size_292_);
if (lean_obj_tag(v_l_296_) == 0)
{
lean_object* v_size_327_; 
v_size_327_ = lean_ctor_get(v_l_296_, 0);
lean_inc(v_size_327_);
v___y_319_ = v_size_327_;
goto v___jp_318_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___y_319_ = v___x_328_;
goto v___jp_318_;
}
v___jp_306_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_nat_add(v___y_307_, v___y_309_);
lean_dec(v___y_309_);
lean_dec(v___y_307_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_r_129_);
lean_ctor_set(v___x_302_, 3, v_r_297_);
lean_ctor_set(v___x_302_, 2, v_v_127_);
lean_ctor_set(v___x_302_, 1, v_k_126_);
lean_ctor_set(v___x_302_, 0, v___x_310_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_r_297_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_r_129_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v___x_312_);
lean_ctor_set(v___x_290_, 3, v___y_308_);
lean_ctor_set(v___x_290_, 2, v_v_295_);
lean_ctor_set(v___x_290_, 1, v_k_294_);
lean_ctor_set(v___x_290_, 0, v___x_305_);
v___x_314_ = v___x_290_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_294_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v___y_308_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
v___jp_318_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_nat_add(v___x_317_, v___y_319_);
lean_dec(v___y_319_);
lean_dec(v___x_317_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v_l_296_);
lean_ctor_set(v___x_131_, 3, v_l_279_);
lean_ctor_set(v___x_131_, 2, v_v_278_);
lean_ctor_set(v___x_131_, 1, v_k_277_);
lean_ctor_set(v___x_131_, 0, v___x_320_);
v___x_322_ = v___x_131_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_k_277_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_v_278_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_l_279_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_l_296_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_nat_add(v___x_274_, v_size_275_);
if (lean_obj_tag(v_r_297_) == 0)
{
lean_object* v_size_324_; 
v_size_324_ = lean_ctor_get(v_r_297_, 0);
lean_inc(v_size_324_);
v___y_307_ = v___x_323_;
v___y_308_ = v___x_322_;
v___y_309_ = v_size_324_;
goto v___jp_306_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___y_307_ = v___x_323_;
v___y_308_ = v___x_322_;
v___y_309_ = v___x_325_;
goto v___jp_306_;
}
}
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_del_object(v___x_131_);
v___x_335_ = lean_nat_add(v___x_274_, v_size_276_);
lean_dec(v_size_276_);
v___x_336_ = lean_nat_add(v___x_335_, v_size_275_);
lean_dec(v___x_335_);
v___x_337_ = lean_nat_add(v___x_274_, v_size_275_);
v___x_338_ = lean_nat_add(v___x_337_, v_size_293_);
lean_dec(v___x_337_);
lean_inc_ref(v_r_129_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_r_129_);
lean_ctor_set(v___x_290_, 3, v_r_280_);
lean_ctor_set(v___x_290_, 2, v_v_127_);
lean_ctor_set(v___x_290_, 1, v_k_126_);
lean_ctor_set(v___x_290_, 0, v___x_338_);
v___x_340_ = v___x_290_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_r_280_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_r_129_);
v___x_340_ = v_reuseFailAlloc_353_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_isSharedCheck_347_ = !lean_is_exclusive(v_r_129_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_348_ = lean_ctor_get(v_r_129_, 4);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_r_129_, 3);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_r_129_, 2);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_r_129_, 1);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_r_129_, 0);
lean_dec(v_unused_352_);
v___x_342_ = v_r_129_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_dec(v_r_129_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v___x_340_);
lean_ctor_set(v___x_342_, 3, v_l_279_);
lean_ctor_set(v___x_342_, 2, v_v_278_);
lean_ctor_set(v___x_342_, 1, v_k_277_);
lean_ctor_set(v___x_342_, 0, v___x_336_);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_277_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_278_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_l_279_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v___x_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_360_; 
v_l_360_ = lean_ctor_get(v_impl_273_, 3);
if (lean_obj_tag(v_l_360_) == 0)
{
lean_object* v_r_361_; lean_object* v_k_362_; lean_object* v_v_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_374_; 
lean_inc_ref(v_l_360_);
v_r_361_ = lean_ctor_get(v_impl_273_, 4);
v_k_362_ = lean_ctor_get(v_impl_273_, 1);
v_v_363_ = lean_ctor_get(v_impl_273_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; lean_object* v_unused_376_; 
v_unused_375_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_376_);
v___x_365_ = v_impl_273_;
v_isShared_366_ = v_isSharedCheck_374_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_r_361_);
lean_inc(v_v_363_);
lean_inc(v_k_362_);
lean_dec(v_impl_273_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_374_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_361_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 3, v_r_361_);
lean_ctor_set(v___x_365_, 2, v_v_127_);
lean_ctor_set(v___x_365_, 1, v_k_126_);
lean_ctor_set(v___x_365_, 0, v___x_274_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_r_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_r_361_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v___x_369_);
lean_ctor_set(v___x_131_, 3, v_l_360_);
lean_ctor_set(v___x_131_, 2, v_v_363_);
lean_ctor_set(v___x_131_, 1, v_k_362_);
lean_ctor_set(v___x_131_, 0, v___x_367_);
v___x_371_ = v___x_131_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_l_360_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_r_377_; 
v_r_377_ = lean_ctor_get(v_impl_273_, 4);
lean_inc(v_r_377_);
if (lean_obj_tag(v_r_377_) == 0)
{
lean_object* v_k_378_; lean_object* v_v_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_402_; 
lean_inc(v_l_360_);
v_k_378_ = lean_ctor_get(v_impl_273_, 1);
v_v_379_ = lean_ctor_get(v_impl_273_, 2);
v_isSharedCheck_402_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; 
v_unused_403_ = lean_ctor_get(v_impl_273_, 4);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_405_);
v___x_381_ = v_impl_273_;
v_isShared_382_ = v_isSharedCheck_402_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_v_379_);
lean_inc(v_k_378_);
lean_dec(v_impl_273_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_402_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_k_383_; lean_object* v_v_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_398_; 
v_k_383_ = lean_ctor_get(v_r_377_, 1);
v_v_384_ = lean_ctor_get(v_r_377_, 2);
v_isSharedCheck_398_ = !lean_is_exclusive(v_r_377_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; lean_object* v_unused_400_; lean_object* v_unused_401_; 
v_unused_399_ = lean_ctor_get(v_r_377_, 4);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_r_377_, 3);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_r_377_, 0);
lean_dec(v_unused_401_);
v___x_386_ = v_r_377_;
v_isShared_387_ = v_isSharedCheck_398_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_v_384_);
lean_inc(v_k_383_);
lean_dec(v_r_377_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_398_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_unsigned_to_nat(3u);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 4, v_l_360_);
lean_ctor_set(v___x_386_, 3, v_l_360_);
lean_ctor_set(v___x_386_, 2, v_v_379_);
lean_ctor_set(v___x_386_, 1, v_k_378_);
lean_ctor_set(v___x_386_, 0, v___x_274_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_k_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_v_379_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_l_360_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_l_360_);
v___x_390_ = v_reuseFailAlloc_397_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 4, v_l_360_);
lean_ctor_set(v___x_381_, 2, v_v_127_);
lean_ctor_set(v___x_381_, 1, v_k_126_);
lean_ctor_set(v___x_381_, 0, v___x_274_);
v___x_392_ = v___x_381_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_l_360_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_l_360_);
v___x_392_ = v_reuseFailAlloc_396_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v___x_392_);
lean_ctor_set(v___x_131_, 3, v___x_390_);
lean_ctor_set(v___x_131_, 2, v_v_384_);
lean_ctor_set(v___x_131_, 1, v_k_383_);
lean_ctor_set(v___x_131_, 0, v___x_388_);
v___x_394_ = v___x_131_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_k_383_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_v_384_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(2u);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v_r_377_);
lean_ctor_set(v___x_131_, 3, v_impl_273_);
lean_ctor_set(v___x_131_, 0, v___x_406_);
v___x_408_ = v___x_131_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_impl_273_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_r_377_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_k_122_);
lean_ctor_set(v___x_412_, 2, v_v_123_);
lean_ctor_set(v___x_412_, 3, v_t_124_);
lean_ctor_set(v___x_412_, 4, v_t_124_);
return v___x_412_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* v_k_413_, lean_object* v_t_414_){
_start:
{
if (lean_obj_tag(v_t_414_) == 0)
{
lean_object* v_k_415_; lean_object* v_l_416_; lean_object* v_r_417_; uint8_t v___x_418_; 
v_k_415_ = lean_ctor_get(v_t_414_, 1);
v_l_416_ = lean_ctor_get(v_t_414_, 3);
v_r_417_ = lean_ctor_get(v_t_414_, 4);
v___x_418_ = lean_nat_dec_lt(v_k_413_, v_k_415_);
if (v___x_418_ == 0)
{
uint8_t v___x_419_; 
v___x_419_ = lean_nat_dec_eq(v_k_413_, v_k_415_);
if (v___x_419_ == 0)
{
v_t_414_ = v_r_417_;
goto _start;
}
else
{
return v___x_419_;
}
}
else
{
v_t_414_ = v_l_416_;
goto _start;
}
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* v_k_423_, lean_object* v_t_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_423_, v_t_424_);
lean_dec(v_t_424_);
lean_dec(v_k_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* v_i_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_442_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_st_ref_get(v_a_431_);
v___x_448_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_429_, v___x_447_);
lean_dec(v___x_447_);
if (v___x_448_ == 0)
{
v___y_442_ = v_a_431_;
goto v___jp_441_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_449_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__0));
v___x_450_ = l_Nat_reprFast(v_i_429_);
v___x_451_ = lean_string_append(v___x_449_, v___x_450_);
lean_dec_ref(v___x_450_);
v___x_452_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__1));
v___x_453_ = lean_string_append(v___x_451_, v___x_452_);
v___x_454_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_453_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
return v___x_454_;
}
v___jp_435_:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_st_ref_put(v___y_436_, v___y_438_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___y_437_);
return v___x_440_;
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = lean_st_ref_take(v___y_442_);
v___x_444_ = lean_box(0);
v___x_445_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_429_, v___x_443_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
v___x_446_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_i_429_, v___x_444_, v___x_443_);
v___y_436_ = v___y_442_;
v___y_437_ = v___x_444_;
v___y_438_ = v___x_446_;
goto v___jp_435_;
}
else
{
lean_dec(v_i_429_);
v___y_436_ = v___y_442_;
v___y_437_ = v___x_444_;
v___y_438_ = v___x_443_;
goto v___jp_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* v_i_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_IR_Checker_markIndex(v_i_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
return v_res_461_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_k_463_, lean_object* v_t_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_463_, v_t_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* v_00_u03b2_466_, lean_object* v_k_467_, lean_object* v_t_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(v_00_u03b2_466_, v_k_467_, v_t_468_);
lean_dec(v_t_468_);
lean_dec(v_k_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(lean_object* v_00_u03b2_471_, lean_object* v_k_472_, lean_object* v_v_473_, lean_object* v_t_474_, lean_object* v_hl_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_472_, v_v_473_, v_t_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* v_x_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_IR_Checker_markIndex(v_x_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* v_x_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_IR_Checker_markVar(v_x_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* v_j_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_IR_Checker_markIndex(v_j_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* v_j_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_IR_Checker_markJP(v_j_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* v_c_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_513_; lean_object* v_env_514_; lean_object* v_decls_515_; lean_object* v___x_516_; 
v___x_513_ = lean_st_ref_get(v_a_511_);
v_env_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_env_514_);
lean_dec(v___x_513_);
v_decls_515_ = lean_ctor_get(v_a_508_, 2);
lean_inc(v_c_507_);
v___x_516_ = l_Lean_IR_findEnvDecl_x27(v_env_514_, v_c_507_, v_decls_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_517_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
v___x_518_ = 1;
v___x_519_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_507_, v___x_518_);
v___x_520_ = lean_string_append(v___x_517_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
v___x_522_ = lean_string_append(v___x_520_, v___x_521_);
v___x_523_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_522_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
return v___x_523_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_c_507_);
v_val_524_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_516_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v___x_516_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 0);
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_val_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* v_c_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_IR_Checker_getDecl(v_c_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* v_x_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
uint8_t v___y_549_; lean_object* v_localCtx_560_; uint8_t v___x_561_; 
v_localCtx_560_ = lean_ctor_get(v_a_543_, 0);
v___x_561_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_560_, v_x_542_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; 
v___x_562_ = l_Lean_IR_LocalContext_isParam(v_localCtx_560_, v_x_542_);
v___y_549_ = v___x_562_;
goto v___jp_548_;
}
else
{
v___y_549_ = v___x_561_;
goto v___jp_548_;
}
v___jp_548_:
{
if (v___y_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_550_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_551_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_552_ = l_Nat_reprFast(v_x_542_);
v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
lean_dec_ref(v___x_552_);
v___x_554_ = lean_string_append(v___x_550_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
v___x_557_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_556_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_x_542_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_IR_Checker_checkVar(v_x_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_localCtx_578_; uint8_t v___x_579_; 
v_localCtx_578_ = lean_ctor_get(v_a_573_, 0);
v___x_579_ = l_Lean_IR_LocalContext_isJP(v_localCtx_578_, v_j_572_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_580_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_581_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_582_ = l_Nat_reprFast(v_j_572_);
v___x_583_ = lean_string_append(v___x_581_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = lean_string_append(v___x_580_, v___x_583_);
lean_dec_ref(v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
v___x_587_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_586_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v_j_572_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_IR_Checker_checkJP(v_j_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
if (lean_obj_tag(v_a_597_) == 0)
{
lean_object* v_id_603_; lean_object* v___x_604_; 
v_id_603_ = lean_ctor_get(v_a_597_, 0);
lean_inc(v_id_603_);
lean_dec_ref_known(v_a_597_, 1);
v___x_604_ = l_Lean_IR_Checker_checkVar(v_id_603_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_IR_Checker_checkArg(v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_614_, size_t v_i_615_, size_t v_stop_616_, lean_object* v_b_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_eq(v_i_615_, v_stop_616_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_array_uget_borrowed(v_as_614_, v_i_615_);
lean_inc(v___x_624_);
v___x_625_ = l_Lean_IR_Checker_checkArg(v___x_624_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; size_t v___x_627_; size_t v___x_628_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_615_, v___x_627_);
v_i_615_ = v___x_628_;
v_b_617_ = v_a_626_;
goto _start;
}
else
{
return v___x_625_;
}
}
else
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_b_617_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_stop_633_, lean_object* v_b_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
size_t v_i_boxed_640_; size_t v_stop_boxed_641_; lean_object* v_res_642_; 
v_i_boxed_640_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_stop_boxed_641_ = lean_unbox_usize(v_stop_633_);
lean_dec(v_stop_633_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_631_, v_i_boxed_640_, v_stop_boxed_641_, v_b_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v_as_631_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_array_get_size(v_as_643_);
v___x_651_ = lean_box(0);
v___x_652_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
return v___x_653_;
}
else
{
uint8_t v___x_654_; 
v___x_654_ = lean_nat_dec_le(v___x_650_, v___x_650_);
if (v___x_654_ == 0)
{
if (v___x_652_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_651_);
return v___x_655_;
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_650_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_643_, v___x_656_, v___x_657_, v___x_651_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_658_;
}
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_650_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_643_, v___x_659_, v___x_660_, v___x_651_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_IR_Checker_checkArgs(v_as_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec_ref(v_as_662_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_670_, lean_object* v_ty_u2082_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_670_, v_ty_u2082_671_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_679_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_678_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_682_, lean_object* v_ty_u2082_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_682_, v_ty_u2082_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_ty_u2082_683_);
lean_dec(v_ty_u2081_682_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_692_, lean_object* v_p_693_, lean_object* v_suffix_x3f_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
lean_inc(v_ty_692_);
v___x_700_ = lean_apply_1(v_p_693_, v_ty_692_);
v___x_701_ = lean_unbox(v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_msg_709_; 
v___x_702_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_703_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_692_);
v___x_704_ = l_Std_Format_defWidth;
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = l_Std_Format_pretty(v___x_703_, v___x_704_, v___x_705_, v___x_705_);
v___x_707_ = lean_string_append(v___x_702_, v___x_706_);
lean_dec_ref(v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_709_ = lean_string_append(v___x_707_, v___x_708_);
if (lean_obj_tag(v_suffix_x3f_694_) == 1)
{
lean_object* v_val_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_msg_713_; lean_object* v___x_714_; 
v_val_710_ = lean_ctor_get(v_suffix_x3f_694_, 0);
v___x_711_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_712_ = lean_string_append(v_msg_709_, v___x_711_);
v_msg_713_ = lean_string_append(v___x_712_, v_val_710_);
v___x_714_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_713_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_709_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
return v___x_715_;
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_ty_692_);
v___x_716_ = lean_box(0);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_718_, lean_object* v_p_719_, lean_object* v_suffix_x3f_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_IR_Checker_checkType(v_ty_718_, v_p_719_, v_suffix_x3f_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_suffix_x3f_720_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = l_Lean_IR_IRType_isObj(v_ty_728_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_msg_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_msg_746_; lean_object* v___x_747_; 
v___x_735_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_736_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_737_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_728_);
v___x_738_ = l_Std_Format_defWidth;
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = l_Std_Format_pretty(v___x_737_, v___x_738_, v___x_739_, v___x_739_);
v___x_741_ = lean_string_append(v___x_736_, v___x_740_);
lean_dec_ref(v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_743_ = lean_string_append(v___x_741_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_745_ = lean_string_append(v_msg_743_, v___x_744_);
v_msg_746_ = lean_string_append(v___x_745_, v___x_735_);
v___x_747_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_746_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec(v_ty_728_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_IR_Checker_checkObjType(v_ty_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = l_Lean_IR_IRType_isScalar(v_ty_758_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_msg_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_msg_776_; lean_object* v___x_777_; 
v___x_765_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_766_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_767_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_758_);
v___x_768_ = l_Std_Format_defWidth;
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_Std_Format_pretty(v___x_767_, v___x_768_, v___x_769_, v___x_769_);
v___x_771_ = lean_string_append(v___x_766_, v___x_770_);
lean_dec_ref(v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_773_ = lean_string_append(v___x_771_, v___x_772_);
v___x_774_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_775_ = lean_string_append(v_msg_773_, v___x_774_);
v_msg_776_ = lean_string_append(v___x_775_, v___x_765_);
v___x_777_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_776_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v_ty_758_);
v___x_778_ = lean_box(0);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_IR_Checker_checkScalarType(v_ty_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_localCtx_793_; lean_object* v___x_794_; 
v_localCtx_793_ = lean_ctor_get(v_a_788_, 0);
v___x_794_ = l_Lean_IR_LocalContext_getType(v_localCtx_793_, v_x_787_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_795_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_796_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_797_ = l_Nat_reprFast(v_x_787_);
v___x_798_ = lean_string_append(v___x_796_, v___x_797_);
lean_dec_ref(v___x_797_);
v___x_799_ = lean_string_append(v___x_795_, v___x_798_);
lean_dec_ref(v___x_798_);
v___x_800_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_801_ = lean_string_append(v___x_799_, v___x_800_);
v___x_802_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_801_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_802_;
}
else
{
lean_object* v_val_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_x_787_);
v_val_803_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_794_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_val_803_);
lean_dec(v___x_794_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 0);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_IR_Checker_getType(v_x_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_818_, lean_object* v_p_819_, lean_object* v_suffix_x3f_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_IR_Checker_getType(v_x_818_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_851_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_851_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_851_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_851_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; uint8_t v___x_832_; 
lean_inc(v_a_827_);
v___x_831_ = lean_apply_1(v_p_819_, v_a_827_);
v___x_832_ = lean_unbox(v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_msg_840_; 
lean_del_object(v___x_829_);
v___x_833_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_834_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_827_);
v___x_835_ = l_Std_Format_defWidth;
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = l_Std_Format_pretty(v___x_834_, v___x_835_, v___x_836_, v___x_836_);
v___x_838_ = lean_string_append(v___x_833_, v___x_837_);
lean_dec_ref(v___x_837_);
v___x_839_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_840_ = lean_string_append(v___x_838_, v___x_839_);
if (lean_obj_tag(v_suffix_x3f_820_) == 1)
{
lean_object* v_val_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_msg_844_; lean_object* v___x_845_; 
v_val_841_ = lean_ctor_get(v_suffix_x3f_820_, 0);
v___x_842_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_843_ = lean_string_append(v_msg_840_, v___x_842_);
v_msg_844_ = lean_string_append(v___x_843_, v_val_841_);
v___x_845_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_844_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_840_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
return v___x_846_;
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_849_; 
lean_dec(v_a_827_);
v___x_847_ = lean_box(0);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_847_);
v___x_849_ = v___x_829_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v_p_819_);
v_a_852_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_826_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_826_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_860_, lean_object* v_p_861_, lean_object* v_suffix_x3f_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_IR_Checker_checkVarType(v_x_860_, v_p_861_, v_suffix_x3f_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_suffix_x3f_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_876_ = l_Lean_IR_Checker_getType(v_x_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_898_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_898_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_898_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_898_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
uint8_t v___x_881_; 
v___x_881_ = l_Lean_IR_IRType_isObj(v_a_877_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_msg_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v_msg_892_; lean_object* v___x_893_; 
lean_del_object(v___x_879_);
v___x_882_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_883_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_877_);
v___x_884_ = l_Std_Format_defWidth;
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = l_Std_Format_pretty(v___x_883_, v___x_884_, v___x_885_, v___x_885_);
v___x_887_ = lean_string_append(v___x_882_, v___x_886_);
lean_dec_ref(v___x_886_);
v___x_888_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_889_ = lean_string_append(v___x_887_, v___x_888_);
v___x_890_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_891_ = lean_string_append(v_msg_889_, v___x_890_);
v_msg_892_ = lean_string_append(v___x_891_, v___x_875_);
v___x_893_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_892_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_896_; 
lean_dec(v_a_877_);
v___x_894_ = lean_box(0);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_894_);
v___x_896_ = v___x_879_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_876_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_876_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_IR_Checker_checkObjVar(v_x_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_921_ = l_Lean_IR_Checker_getType(v_x_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_943_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_943_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_943_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_943_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
uint8_t v___x_926_; 
v___x_926_ = l_Lean_IR_IRType_isScalar(v_a_922_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_msg_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_msg_937_; lean_object* v___x_938_; 
lean_del_object(v___x_924_);
v___x_927_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_928_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_922_);
v___x_929_ = l_Std_Format_defWidth;
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = l_Std_Format_pretty(v___x_928_, v___x_929_, v___x_930_, v___x_930_);
v___x_932_ = lean_string_append(v___x_927_, v___x_931_);
lean_dec_ref(v___x_931_);
v___x_933_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_934_ = lean_string_append(v___x_932_, v___x_933_);
v___x_935_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_936_ = lean_string_append(v_msg_934_, v___x_935_);
v_msg_937_ = lean_string_append(v___x_936_, v___x_920_);
v___x_938_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_937_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_941_; 
lean_dec(v_a_922_);
v___x_939_ = lean_box(0);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_939_);
v___x_941_ = v___x_924_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_944_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_921_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_921_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_IR_Checker_checkScalarVar(v_x_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_963_, lean_object* v_ys_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; 
lean_inc(v_c_963_);
v___x_970_ = l_Lean_IR_Checker_getDecl(v_c_963_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = lean_array_get_size(v_ys_964_);
v___x_973_ = l_Lean_IR_Decl_params(v_a_971_);
lean_dec(v_a_971_);
v___x_974_ = lean_array_get_size(v___x_973_);
lean_dec_ref(v___x_973_);
v___x_975_ = lean_nat_dec_eq(v___x_972_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_976_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_977_ = 1;
v___x_978_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_963_, v___x_977_);
v___x_979_ = lean_string_append(v___x_976_, v___x_978_);
lean_dec_ref(v___x_978_);
v___x_980_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
v___x_982_ = l_Nat_reprFast(v___x_972_);
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v___x_986_ = l_Nat_reprFast(v___x_974_);
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
lean_dec_ref(v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_989_ = lean_string_append(v___x_987_, v___x_988_);
v___x_990_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_989_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; 
lean_dec(v_c_963_);
v___x_991_ = l_Lean_IR_Checker_checkArgs(v_ys_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_991_;
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v_c_963_);
v_a_992_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_970_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_970_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_1000_, lean_object* v_ys_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_IR_Checker_checkFullApp(v_c_1000_, v_ys_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec_ref(v_ys_1001_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1011_, lean_object* v_ys_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1018_; 
lean_inc(v_c_1011_);
v___x_1018_ = l_Lean_IR_Checker_getDecl(v_c_1011_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = lean_array_get_size(v_ys_1012_);
v___x_1021_ = l_Lean_IR_Decl_params(v_a_1019_);
lean_dec(v_a_1019_);
v___x_1022_ = lean_array_get_size(v___x_1021_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = lean_nat_dec_lt(v___x_1020_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1024_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1025_ = 1;
v___x_1026_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1011_, v___x_1025_);
v___x_1027_ = lean_string_append(v___x_1024_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
v___x_1030_ = l_Nat_reprFast(v___x_1020_);
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
v___x_1034_ = l_Nat_reprFast(v___x_1022_);
v___x_1035_ = lean_string_append(v___x_1033_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1035_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_c_1011_);
v___x_1037_ = l_Lean_IR_Checker_checkArgs(v_ys_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
return v___x_1037_;
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_c_1011_);
v_a_1038_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1018_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1018_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1046_, lean_object* v_ys_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_IR_Checker_checkPartialApp(v_c_1046_, v_ys_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec_ref(v_ys_1047_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1061_, lean_object* v_e_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
switch(lean_obj_tag(v_e_1062_))
{
case 0:
{
lean_object* v_i_1068_; lean_object* v_ys_1069_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v_name_1080_; lean_object* v_cidx_1081_; lean_object* v_size_1082_; lean_object* v_usize_1083_; lean_object* v_ssize_1084_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_i_1068_ = lean_ctor_get(v_e_1062_, 0);
lean_inc_ref(v_i_1068_);
v_ys_1069_ = lean_ctor_get(v_e_1062_, 1);
lean_inc_ref(v_ys_1069_);
lean_dec_ref_known(v_e_1062_, 2);
v_name_1080_ = lean_ctor_get(v_i_1068_, 0);
v_cidx_1081_ = lean_ctor_get(v_i_1068_, 1);
v_size_1082_ = lean_ctor_get(v_i_1068_, 2);
v_usize_1083_ = lean_ctor_get(v_i_1068_, 3);
v_ssize_1084_ = lean_ctor_get(v_i_1068_, 4);
v___x_1116_ = l_Lean_maxCtorTag;
v___x_1117_ = lean_nat_dec_lt(v___x_1116_, v_cidx_1081_);
if (v___x_1117_ == 0)
{
v___y_1103_ = v_a_1063_;
v___y_1104_ = v_a_1064_;
v___y_1105_ = v_a_1065_;
v___y_1106_ = v_a_1066_;
goto v___jp_1102_;
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = l_Lean_IR_CtorInfo_isRef(v_i_1068_);
if (v___x_1118_ == 0)
{
v___y_1103_ = v_a_1063_;
v___y_1104_ = v_a_1064_;
v___y_1105_ = v_a_1065_;
v___y_1106_ = v_a_1066_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_inc(v_name_1080_);
lean_dec_ref(v_ys_1069_);
lean_dec_ref(v_i_1068_);
lean_dec(v_ty_1061_);
v___x_1119_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1120_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1080_, v___x_1118_);
v___x_1121_ = lean_string_append(v___x_1119_, v___x_1120_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1123_ = lean_string_append(v___x_1121_, v___x_1122_);
v___x_1124_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1123_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1124_;
}
}
v___jp_1070_:
{
uint8_t v___x_1075_; 
v___x_1075_ = l_Lean_IR_CtorInfo_isRef(v_i_1068_);
lean_dec_ref(v_i_1068_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec_ref(v_ys_1069_);
lean_dec(v_ty_1061_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v___x_1079_; 
lean_dec_ref_known(v___x_1078_, 1);
v___x_1079_ = l_Lean_IR_Checker_checkArgs(v_ys_1069_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec_ref(v_ys_1069_);
return v___x_1079_;
}
else
{
lean_dec_ref(v_ys_1069_);
return v___x_1078_;
}
}
}
v___jp_1085_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1090_ = l_Lean_usizeSize;
v___x_1091_ = lean_nat_mul(v_usize_1083_, v___x_1090_);
v___x_1092_ = lean_nat_add(v_ssize_1084_, v___x_1091_);
lean_dec(v___x_1091_);
v___x_1093_ = l_Lean_maxCtorScalarsSize;
v___x_1094_ = lean_nat_dec_lt(v___x_1092_, v___x_1093_);
lean_dec(v___x_1092_);
if (v___x_1094_ == 0)
{
uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_inc(v_name_1080_);
lean_dec_ref(v_ys_1069_);
lean_dec_ref(v_i_1068_);
lean_dec(v_ty_1061_);
v___x_1095_ = 1;
v___x_1096_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1097_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1080_, v___x_1095_);
v___x_1098_ = lean_string_append(v___x_1096_, v___x_1097_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1100_ = lean_string_append(v___x_1098_, v___x_1099_);
v___x_1101_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1100_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1101_;
}
else
{
v___y_1071_ = v___y_1086_;
v___y_1072_ = v___y_1087_;
v___y_1073_ = v___y_1088_;
v___y_1074_ = v___y_1089_;
goto v___jp_1070_;
}
}
v___jp_1102_:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = l_Lean_maxCtorFields;
v___x_1108_ = lean_nat_dec_lt(v_size_1082_, v___x_1107_);
if (v___x_1108_ == 0)
{
uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_inc(v_name_1080_);
lean_dec_ref(v_ys_1069_);
lean_dec_ref(v_i_1068_);
lean_dec(v_ty_1061_);
v___x_1109_ = 1;
v___x_1110_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1111_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1080_, v___x_1109_);
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
lean_dec_ref(v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1114_ = lean_string_append(v___x_1112_, v___x_1113_);
v___x_1115_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1114_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
return v___x_1115_;
}
else
{
v___y_1086_ = v___y_1103_;
v___y_1087_ = v___y_1104_;
v___y_1088_ = v___y_1105_;
v___y_1089_ = v___y_1106_;
goto v___jp_1085_;
}
}
}
case 1:
{
lean_object* v_x_1125_; lean_object* v___x_1126_; 
v_x_1125_ = lean_ctor_get(v_e_1062_, 1);
lean_inc(v_x_1125_);
lean_dec_ref_known(v_e_1062_, 2);
v___x_1126_ = l_Lean_IR_Checker_checkObjVar(v_x_1125_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref_known(v___x_1126_, 1);
v___x_1127_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1127_;
}
else
{
lean_dec(v_ty_1061_);
return v___x_1126_;
}
}
case 2:
{
lean_object* v_x_1128_; lean_object* v_ys_1129_; lean_object* v___x_1130_; 
v_x_1128_ = lean_ctor_get(v_e_1062_, 0);
lean_inc(v_x_1128_);
v_ys_1129_ = lean_ctor_get(v_e_1062_, 2);
lean_inc_ref(v_ys_1129_);
lean_dec_ref_known(v_e_1062_, 3);
v___x_1130_ = l_Lean_IR_Checker_checkObjVar(v_x_1128_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref_known(v___x_1130_, 1);
v___x_1131_ = l_Lean_IR_Checker_checkArgs(v_ys_1129_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec_ref(v_ys_1129_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1131_, 1);
v___x_1132_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1132_;
}
else
{
lean_dec(v_ty_1061_);
return v___x_1131_;
}
}
else
{
lean_dec_ref(v_ys_1129_);
lean_dec(v_ty_1061_);
return v___x_1130_;
}
}
case 3:
{
lean_object* v_i_1133_; lean_object* v_x_1134_; lean_object* v___x_1135_; 
v_i_1133_ = lean_ctor_get(v_e_1062_, 0);
lean_inc(v_i_1133_);
v_x_1134_ = lean_ctor_get(v_e_1062_, 1);
lean_inc(v_x_1134_);
lean_dec_ref_known(v_e_1062_, 2);
v___x_1135_ = l_Lean_IR_Checker_getType(v_x_1134_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1181_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1181_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1181_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
switch(lean_obj_tag(v_a_1136_))
{
case 7:
{
lean_object* v___x_1140_; 
lean_del_object(v___x_1138_);
lean_dec(v_i_1133_);
v___x_1140_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1140_;
}
case 8:
{
lean_object* v___x_1141_; 
lean_del_object(v___x_1138_);
lean_dec(v_i_1133_);
v___x_1141_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1141_;
}
case 10:
{
lean_object* v_types_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_types_1142_ = lean_ctor_get(v_a_1136_, 1);
lean_inc_ref(v_types_1142_);
lean_dec_ref_known(v_a_1136_, 2);
v___x_1143_ = lean_array_get_size(v_types_1142_);
v___x_1144_ = lean_nat_dec_lt(v_i_1133_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_types_1142_);
lean_del_object(v___x_1138_);
lean_dec(v_i_1133_);
lean_dec(v_ty_1061_);
v___x_1145_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1146_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1145_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_array_fget(v_types_1142_, v_i_1133_);
lean_dec(v_i_1133_);
lean_dec_ref(v_types_1142_);
v___x_1148_ = l_Lean_IR_instBEqIRType_beq(v___x_1147_, v_ty_1061_);
lean_dec(v_ty_1061_);
lean_dec(v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_del_object(v___x_1138_);
v___x_1149_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1150_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1149_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_box(0);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1151_);
v___x_1153_ = v___x_1138_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
case 11:
{
lean_object* v_types_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_types_1155_ = lean_ctor_get(v_a_1136_, 1);
lean_inc_ref(v_types_1155_);
lean_dec_ref_known(v_a_1136_, 2);
v___x_1156_ = lean_array_get_size(v_types_1155_);
v___x_1157_ = lean_nat_dec_lt(v_i_1133_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec_ref(v_types_1155_);
lean_del_object(v___x_1138_);
lean_dec(v_i_1133_);
lean_dec(v_ty_1061_);
v___x_1158_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1159_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1158_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_array_fget(v_types_1155_, v_i_1133_);
lean_dec(v_i_1133_);
lean_dec_ref(v_types_1155_);
v___x_1161_ = l_Lean_IR_instBEqIRType_beq(v___x_1160_, v_ty_1061_);
lean_dec(v_ty_1061_);
lean_dec(v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_del_object(v___x_1138_);
v___x_1162_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1163_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1162_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(0);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1164_);
v___x_1166_ = v___x_1138_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
case 12:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_dec(v_i_1133_);
lean_dec(v_ty_1061_);
v___x_1168_ = lean_box(0);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1168_);
v___x_1170_ = v___x_1138_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
default: 
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_del_object(v___x_1138_);
lean_dec(v_i_1133_);
lean_dec(v_ty_1061_);
v___x_1172_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1173_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1136_);
v___x_1174_ = l_Std_Format_defWidth;
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = l_Std_Format_pretty(v___x_1173_, v___x_1174_, v___x_1175_, v___x_1175_);
v___x_1177_ = lean_string_append(v___x_1172_, v___x_1176_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
v___x_1180_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1179_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1180_;
}
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_i_1133_);
lean_dec(v_ty_1061_);
v_a_1182_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1135_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1135_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
case 4:
{
lean_object* v_x_1190_; lean_object* v___x_1191_; 
v_x_1190_ = lean_ctor_get(v_e_1062_, 1);
lean_inc(v_x_1190_);
lean_dec_ref_known(v_e_1062_, 2);
v___x_1191_ = l_Lean_IR_Checker_checkObjVar(v_x_1190_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1210_; 
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v___x_1191_, 0);
lean_dec(v_unused_1211_);
v___x_1193_ = v___x_1191_;
v_isShared_1194_ = v_isSharedCheck_1210_;
goto v_resetjp_1192_;
}
else
{
lean_dec(v___x_1191_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1210_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_box(5);
v___x_1196_ = l_Lean_IR_instBEqIRType_beq(v_ty_1061_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_msg_1204_; lean_object* v___x_1205_; 
lean_del_object(v___x_1193_);
v___x_1197_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1198_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1061_);
v___x_1199_ = l_Std_Format_defWidth;
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = l_Std_Format_pretty(v___x_1198_, v___x_1199_, v___x_1200_, v___x_1200_);
v___x_1202_ = lean_string_append(v___x_1197_, v___x_1201_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
v___x_1205_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1204_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_dec(v_ty_1061_);
v___x_1206_ = lean_box(0);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1206_);
v___x_1208_ = v___x_1193_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_dec(v_ty_1061_);
return v___x_1191_;
}
}
case 5:
{
lean_object* v_x_1212_; lean_object* v___x_1213_; 
v_x_1212_ = lean_ctor_get(v_e_1062_, 2);
lean_inc(v_x_1212_);
lean_dec_ref_known(v_e_1062_, 3);
v___x_1213_ = l_Lean_IR_Checker_checkObjVar(v_x_1212_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1214_; 
lean_dec_ref_known(v___x_1213_, 1);
v___x_1214_ = l_Lean_IR_Checker_checkScalarType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1214_;
}
else
{
lean_dec(v_ty_1061_);
return v___x_1213_;
}
}
case 6:
{
lean_object* v_c_1215_; lean_object* v_ys_1216_; lean_object* v___x_1217_; 
lean_dec(v_ty_1061_);
v_c_1215_ = lean_ctor_get(v_e_1062_, 0);
lean_inc(v_c_1215_);
v_ys_1216_ = lean_ctor_get(v_e_1062_, 1);
lean_inc_ref(v_ys_1216_);
lean_dec_ref_known(v_e_1062_, 2);
v___x_1217_ = l_Lean_IR_Checker_checkFullApp(v_c_1215_, v_ys_1216_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec_ref(v_ys_1216_);
return v___x_1217_;
}
case 7:
{
lean_object* v_c_1218_; lean_object* v_ys_1219_; lean_object* v___x_1220_; 
v_c_1218_ = lean_ctor_get(v_e_1062_, 0);
lean_inc(v_c_1218_);
v_ys_1219_ = lean_ctor_get(v_e_1062_, 1);
lean_inc_ref(v_ys_1219_);
lean_dec_ref_known(v_e_1062_, 2);
v___x_1220_ = l_Lean_IR_Checker_checkPartialApp(v_c_1218_, v_ys_1219_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec_ref(v_ys_1219_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1221_; 
lean_dec_ref_known(v___x_1220_, 1);
v___x_1221_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1221_;
}
else
{
lean_dec(v_ty_1061_);
return v___x_1220_;
}
}
case 8:
{
lean_object* v_x_1222_; lean_object* v_ys_1223_; lean_object* v___x_1224_; 
v_x_1222_ = lean_ctor_get(v_e_1062_, 0);
lean_inc(v_x_1222_);
v_ys_1223_ = lean_ctor_get(v_e_1062_, 1);
lean_inc_ref(v_ys_1223_);
lean_dec_ref_known(v_e_1062_, 2);
v___x_1224_ = l_Lean_IR_Checker_checkObjVar(v_x_1222_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref_known(v___x_1224_, 1);
v___x_1225_ = l_Lean_IR_Checker_checkArgs(v_ys_1223_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec_ref(v_ys_1223_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref_known(v___x_1225_, 1);
v___x_1226_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1226_;
}
else
{
lean_dec(v_ty_1061_);
return v___x_1225_;
}
}
else
{
lean_dec_ref(v_ys_1223_);
lean_dec(v_ty_1061_);
return v___x_1224_;
}
}
case 9:
{
lean_object* v_ty_1227_; lean_object* v_x_1228_; lean_object* v___x_1229_; 
v_ty_1227_ = lean_ctor_get(v_e_1062_, 0);
lean_inc(v_ty_1227_);
v_x_1228_ = lean_ctor_get(v_e_1062_, 1);
lean_inc(v_x_1228_);
lean_dec_ref_known(v_e_1062_, 2);
v___x_1229_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref_known(v___x_1229_, 1);
lean_inc(v_x_1228_);
v___x_1230_ = l_Lean_IR_Checker_checkScalarVar(v_x_1228_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1231_; 
lean_dec_ref_known(v___x_1230_, 1);
v___x_1231_ = l_Lean_IR_Checker_getType(v_x_1228_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1250_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1250_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1250_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
uint8_t v___x_1236_; 
v___x_1236_ = l_Lean_IR_instBEqIRType_beq(v_a_1232_, v_ty_1227_);
lean_dec(v_ty_1227_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_msg_1244_; lean_object* v___x_1245_; 
lean_del_object(v___x_1234_);
v___x_1237_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1238_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1232_);
v___x_1239_ = l_Std_Format_defWidth;
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = l_Std_Format_pretty(v___x_1238_, v___x_1239_, v___x_1240_, v___x_1240_);
v___x_1242_ = lean_string_append(v___x_1237_, v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1244_ = lean_string_append(v___x_1242_, v___x_1243_);
v___x_1245_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1244_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_dec(v_a_1232_);
v___x_1246_ = lean_box(0);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1246_);
v___x_1248_ = v___x_1234_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_ty_1227_);
v_a_1251_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1231_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1231_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_dec(v_x_1228_);
lean_dec(v_ty_1227_);
return v___x_1230_;
}
}
else
{
lean_dec(v_x_1228_);
lean_dec(v_ty_1227_);
return v___x_1229_;
}
}
case 10:
{
lean_object* v_x_1259_; lean_object* v___x_1260_; 
v_x_1259_ = lean_ctor_get(v_e_1062_, 0);
lean_inc(v_x_1259_);
lean_dec_ref_known(v_e_1062_, 1);
v___x_1260_ = l_Lean_IR_Checker_checkScalarType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref_known(v___x_1260_, 1);
v___x_1261_ = l_Lean_IR_Checker_checkObjVar(v_x_1259_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1261_;
}
else
{
lean_dec(v_x_1259_);
return v___x_1260_;
}
}
case 11:
{
lean_object* v_v_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1271_; 
v_v_1262_ = lean_ctor_get(v_e_1062_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_e_1062_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1264_ = v_e_1062_;
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_v_1262_);
lean_dec(v_e_1062_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
if (lean_obj_tag(v_v_1262_) == 1)
{
lean_object* v___x_1266_; 
lean_dec_ref_known(v_v_1262_, 1);
lean_del_object(v___x_1264_);
v___x_1266_ = l_Lean_IR_Checker_checkObjType(v_ty_1061_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
lean_dec_ref(v_v_1262_);
lean_dec(v_ty_1061_);
v___x_1267_ = lean_box(0);
if (v_isShared_1265_ == 0)
{
lean_ctor_set_tag(v___x_1264_, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1267_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
default: 
{
lean_object* v_x_1272_; lean_object* v___x_1273_; 
v_x_1272_ = lean_ctor_get(v_e_1062_, 0);
lean_inc(v_x_1272_);
lean_dec_ref_known(v_e_1062_, 1);
v___x_1273_ = l_Lean_IR_Checker_checkObjVar(v_x_1272_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1292_; 
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1273_, 0);
lean_dec(v_unused_1293_);
v___x_1275_ = v___x_1273_;
v_isShared_1276_ = v_isSharedCheck_1292_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v___x_1273_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1292_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_box(1);
v___x_1278_ = l_Lean_IR_instBEqIRType_beq(v_ty_1061_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_msg_1286_; lean_object* v___x_1287_; 
lean_del_object(v___x_1275_);
v___x_1279_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1280_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1061_);
v___x_1281_ = l_Std_Format_defWidth;
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = l_Std_Format_pretty(v___x_1280_, v___x_1281_, v___x_1282_, v___x_1282_);
v___x_1284_ = lean_string_append(v___x_1279_, v___x_1283_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1286_ = lean_string_append(v___x_1284_, v___x_1285_);
v___x_1287_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1286_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_dec(v_ty_1061_);
v___x_1288_ = lean_box(0);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1288_);
v___x_1290_ = v___x_1275_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_dec(v_ty_1061_);
return v___x_1273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1294_, lean_object* v_e_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_IR_Checker_checkExpr(v_ty_1294_, v_e_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1302_, lean_object* v_p_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_x_1309_; lean_object* v___x_1310_; 
v_x_1309_ = lean_ctor_get(v_p_1303_, 0);
lean_inc(v_x_1309_);
v___x_1310_ = l_Lean_IR_Checker_markIndex(v_x_1309_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v___x_1310_, 0);
lean_dec(v_unused_1319_);
v___x_1312_ = v___x_1310_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v___x_1310_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = l_Lean_IR_LocalContext_addParam(v_ctx_1302_, v_p_1303_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_p_1303_);
lean_dec(v_ctx_1302_);
v_a_1320_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1310_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1310_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1328_, lean_object* v_p_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1328_, v_p_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1335_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_instMonadEIO___redArg();
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1338_ = l_StateRefT_x27_instMonad___redArg(v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1342_, lean_object* v_k_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v_toApplicative_1350_; lean_object* v_toFunctor_1351_; lean_object* v_toSeq_1352_; lean_object* v_toSeqLeft_1353_; lean_object* v_toSeqRight_1354_; lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___f_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_localCtx_1367_; lean_object* v_currentDecl_1368_; lean_object* v_decls_1369_; lean_object* v_a_1371_; lean_object* v___y_1375_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1349_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1350_ = lean_ctor_get(v___x_1349_, 0);
v_toFunctor_1351_ = lean_ctor_get(v_toApplicative_1350_, 0);
v_toSeq_1352_ = lean_ctor_get(v_toApplicative_1350_, 2);
v_toSeqLeft_1353_ = lean_ctor_get(v_toApplicative_1350_, 3);
v_toSeqRight_1354_ = lean_ctor_get(v_toApplicative_1350_, 4);
v___f_1355_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1356_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1351_, 2);
v___f_1357_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1357_, 0, v_toFunctor_1351_);
v___f_1358_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1358_, 0, v_toFunctor_1351_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___f_1357_);
lean_ctor_set(v___x_1359_, 1, v___f_1358_);
lean_inc(v_toSeqRight_1354_);
v___f_1360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1360_, 0, v_toSeqRight_1354_);
lean_inc(v_toSeqLeft_1353_);
v___f_1361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1361_, 0, v_toSeqLeft_1353_);
lean_inc(v_toSeq_1352_);
v___f_1362_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1362_, 0, v_toSeq_1352_);
v___x_1363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1359_);
lean_ctor_set(v___x_1363_, 1, v___f_1355_);
lean_ctor_set(v___x_1363_, 2, v___f_1362_);
lean_ctor_set(v___x_1363_, 3, v___f_1361_);
lean_ctor_set(v___x_1363_, 4, v___f_1360_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v___f_1356_);
v___x_1365_ = l_StateRefT_x27_instMonad___redArg(v___x_1364_);
v___x_1366_ = l_ReaderT_instMonad___redArg(v___x_1365_);
v_localCtx_1367_ = lean_ctor_get(v_a_1344_, 0);
v_currentDecl_1368_ = lean_ctor_get(v_a_1344_, 1);
v_decls_1369_ = lean_ctor_get(v_a_1344_, 2);
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_array_get_size(v_ps_1342_);
v___x_1387_ = lean_nat_dec_lt(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_dec_ref(v___x_1366_);
lean_dec_ref(v_ps_1342_);
lean_inc(v_localCtx_1367_);
v_a_1371_ = v_localCtx_1367_;
goto v___jp_1370_;
}
else
{
lean_object* v___f_1388_; uint8_t v___x_1389_; 
v___f_1388_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1389_ = lean_nat_dec_le(v___x_1386_, v___x_1386_);
if (v___x_1389_ == 0)
{
if (v___x_1387_ == 0)
{
lean_dec_ref(v___x_1366_);
lean_dec_ref(v_ps_1342_);
lean_inc(v_localCtx_1367_);
v_a_1371_ = v_localCtx_1367_;
goto v___jp_1370_;
}
else
{
size_t v___x_1390_; size_t v___x_1391_; lean_object* v___x_1038__overap_1392_; lean_object* v___x_1393_; 
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = lean_usize_of_nat(v___x_1386_);
lean_inc(v_localCtx_1367_);
v___x_1038__overap_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1366_, v___f_1388_, v_ps_1342_, v___x_1390_, v___x_1391_, v_localCtx_1367_);
lean_inc(v_a_1347_);
lean_inc_ref(v_a_1346_);
lean_inc(v_a_1345_);
lean_inc_ref(v_a_1344_);
v___x_1393_ = lean_apply_5(v___x_1038__overap_1392_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, lean_box(0));
v___y_1375_ = v___x_1393_;
goto v___jp_1374_;
}
}
else
{
size_t v___x_1394_; size_t v___x_1395_; lean_object* v___x_1042__overap_1396_; lean_object* v___x_1397_; 
v___x_1394_ = ((size_t)0ULL);
v___x_1395_ = lean_usize_of_nat(v___x_1386_);
lean_inc(v_localCtx_1367_);
v___x_1042__overap_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1366_, v___f_1388_, v_ps_1342_, v___x_1394_, v___x_1395_, v_localCtx_1367_);
lean_inc(v_a_1347_);
lean_inc_ref(v_a_1346_);
lean_inc(v_a_1345_);
lean_inc_ref(v_a_1344_);
v___x_1397_ = lean_apply_5(v___x_1042__overap_1396_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, lean_box(0));
v___y_1375_ = v___x_1397_;
goto v___jp_1374_;
}
}
v___jp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_inc_ref(v_decls_1369_);
lean_inc_ref(v_currentDecl_1368_);
v___x_1372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1372_, 0, v_a_1371_);
lean_ctor_set(v___x_1372_, 1, v_currentDecl_1368_);
lean_ctor_set(v___x_1372_, 2, v_decls_1369_);
lean_inc(v_a_1347_);
lean_inc_ref(v_a_1346_);
lean_inc(v_a_1345_);
v___x_1373_ = lean_apply_5(v_k_1343_, v___x_1372_, v_a_1345_, v_a_1346_, v_a_1347_, lean_box(0));
return v___x_1373_;
}
v___jp_1374_:
{
if (lean_obj_tag(v___y_1375_) == 0)
{
lean_object* v_a_1376_; 
v_a_1376_ = lean_ctor_get(v___y_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___y_1375_, 1);
v_a_1371_ = v_a_1376_;
goto v___jp_1370_;
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_k_1343_);
v_a_1377_ = lean_ctor_get(v___y_1375_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___y_1375_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___y_1375_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___y_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1398_, lean_object* v_k_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_IR_Checker_withParams(v_ps_1398_, v_k_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1406_, size_t v_i_1407_, size_t v_stop_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_usize_dec_eq(v_i_1407_, v_stop_1408_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v_x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_array_uget_borrowed(v_as_1406_, v_i_1407_);
v_x_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_x_1417_);
v___x_1418_ = l_Lean_IR_Checker_markIndex(v_x_1417_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; 
lean_dec_ref_known(v___x_1418_, 1);
lean_inc(v___x_1416_);
v___x_1419_ = l_Lean_IR_LocalContext_addParam(v_b_1409_, v___x_1416_);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_i_1407_, v___x_1420_);
v_i_1407_ = v___x_1421_;
v_b_1409_ = v___x_1419_;
goto _start;
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_b_1409_);
v_a_1423_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1418_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1418_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_b_1409_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1432_, lean_object* v_i_1433_, lean_object* v_stop_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
size_t v_i_boxed_1441_; size_t v_stop_boxed_1442_; lean_object* v_res_1443_; 
v_i_boxed_1441_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_stop_boxed_1442_ = lean_unbox_usize(v_stop_1434_);
lean_dec(v_stop_1434_);
v_res_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1432_, v_i_boxed_1441_, v_stop_boxed_1442_, v_b_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_as_1432_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_x_1451_; lean_object* v_b_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; 
switch(lean_obj_tag(v_fnBody_1444_))
{
case 0:
{
lean_object* v_x_1459_; lean_object* v_ty_1460_; lean_object* v_e_1461_; lean_object* v_b_1462_; lean_object* v___x_1463_; 
v_x_1459_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_x_1459_);
v_ty_1460_ = lean_ctor_get(v_fnBody_1444_, 1);
lean_inc_n(v_ty_1460_, 2);
v_e_1461_ = lean_ctor_get(v_fnBody_1444_, 2);
lean_inc_ref_n(v_e_1461_, 2);
v_b_1462_ = lean_ctor_get(v_fnBody_1444_, 3);
lean_inc(v_b_1462_);
lean_dec_ref_known(v_fnBody_1444_, 4);
v___x_1463_ = l_Lean_IR_Checker_checkExpr(v_ty_1460_, v_e_1461_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1463_, 1);
lean_inc(v_x_1459_);
v___x_1464_ = l_Lean_IR_Checker_markIndex(v_x_1459_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_localCtx_1465_; lean_object* v_currentDecl_1466_; lean_object* v_decls_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref_known(v___x_1464_, 1);
v_localCtx_1465_ = lean_ctor_get(v_a_1445_, 0);
lean_inc(v_localCtx_1465_);
v_currentDecl_1466_ = lean_ctor_get(v_a_1445_, 1);
lean_inc_ref(v_currentDecl_1466_);
v_decls_1467_ = lean_ctor_get(v_a_1445_, 2);
lean_inc_ref(v_decls_1467_);
lean_dec_ref(v_a_1445_);
v___x_1468_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1465_, v_x_1459_, v_ty_1460_, v_e_1461_);
v___x_1469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_currentDecl_1466_);
lean_ctor_set(v___x_1469_, 2, v_decls_1467_);
v_fnBody_1444_ = v_b_1462_;
v_a_1445_ = v___x_1469_;
goto _start;
}
else
{
lean_dec(v_b_1462_);
lean_dec_ref(v_e_1461_);
lean_dec(v_ty_1460_);
lean_dec(v_x_1459_);
lean_dec_ref(v_a_1445_);
return v___x_1464_;
}
}
else
{
lean_dec(v_b_1462_);
lean_dec_ref(v_e_1461_);
lean_dec(v_ty_1460_);
lean_dec(v_x_1459_);
lean_dec_ref(v_a_1445_);
return v___x_1463_;
}
}
case 1:
{
lean_object* v_j_1471_; lean_object* v_xs_1472_; lean_object* v_v_1473_; lean_object* v_b_1474_; lean_object* v_a_1476_; lean_object* v___x_1485_; 
v_j_1471_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc_n(v_j_1471_, 2);
v_xs_1472_ = lean_ctor_get(v_fnBody_1444_, 1);
lean_inc_ref(v_xs_1472_);
v_v_1473_ = lean_ctor_get(v_fnBody_1444_, 2);
lean_inc(v_v_1473_);
v_b_1474_ = lean_ctor_get(v_fnBody_1444_, 3);
lean_inc(v_b_1474_);
lean_dec_ref_known(v_fnBody_1444_, 4);
v___x_1485_ = l_Lean_IR_Checker_markIndex(v_j_1471_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_localCtx_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
lean_dec_ref_known(v___x_1485_, 1);
v_localCtx_1486_ = lean_ctor_get(v_a_1445_, 0);
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = lean_array_get_size(v_xs_1472_);
v___x_1489_ = lean_nat_dec_lt(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_inc(v_localCtx_1486_);
v_a_1476_ = v_localCtx_1486_;
goto v___jp_1475_;
}
else
{
size_t v___x_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = lean_usize_of_nat(v___x_1488_);
lean_inc(v_localCtx_1486_);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1472_, v___x_1490_, v___x_1491_, v_localCtx_1486_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v_a_1476_ = v_a_1493_;
goto v___jp_1475_;
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_b_1474_);
lean_dec(v_v_1473_);
lean_dec_ref(v_xs_1472_);
lean_dec(v_j_1471_);
lean_dec_ref(v_a_1445_);
v_a_1494_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1492_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1492_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
else
{
lean_dec(v_b_1474_);
lean_dec(v_v_1473_);
lean_dec_ref(v_xs_1472_);
lean_dec(v_j_1471_);
lean_dec_ref(v_a_1445_);
return v___x_1485_;
}
v___jp_1475_:
{
lean_object* v_localCtx_1477_; lean_object* v_currentDecl_1478_; lean_object* v_decls_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_localCtx_1477_ = lean_ctor_get(v_a_1445_, 0);
lean_inc(v_localCtx_1477_);
v_currentDecl_1478_ = lean_ctor_get(v_a_1445_, 1);
lean_inc_ref_n(v_currentDecl_1478_, 2);
v_decls_1479_ = lean_ctor_get(v_a_1445_, 2);
lean_inc_ref_n(v_decls_1479_, 2);
lean_dec_ref(v_a_1445_);
v___x_1480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1480_, 0, v_a_1476_);
lean_ctor_set(v___x_1480_, 1, v_currentDecl_1478_);
lean_ctor_set(v___x_1480_, 2, v_decls_1479_);
lean_inc(v_v_1473_);
v___x_1481_ = l_Lean_IR_Checker_checkFnBody(v_v_1473_, v___x_1480_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref_known(v___x_1481_, 1);
v___x_1482_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1477_, v_j_1471_, v_xs_1472_, v_v_1473_);
v___x_1483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v_currentDecl_1478_);
lean_ctor_set(v___x_1483_, 2, v_decls_1479_);
v_fnBody_1444_ = v_b_1474_;
v_a_1445_ = v___x_1483_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1479_);
lean_dec_ref(v_currentDecl_1478_);
lean_dec(v_localCtx_1477_);
lean_dec(v_b_1474_);
lean_dec(v_v_1473_);
lean_dec_ref(v_xs_1472_);
lean_dec(v_j_1471_);
return v___x_1481_;
}
}
}
case 2:
{
lean_object* v_x_1502_; lean_object* v_y_1503_; lean_object* v_b_1504_; lean_object* v___x_1505_; 
v_x_1502_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_x_1502_);
v_y_1503_ = lean_ctor_get(v_fnBody_1444_, 2);
lean_inc(v_y_1503_);
v_b_1504_ = lean_ctor_get(v_fnBody_1444_, 3);
lean_inc(v_b_1504_);
lean_dec_ref_known(v_fnBody_1444_, 4);
v___x_1505_ = l_Lean_IR_Checker_checkVar(v_x_1502_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1506_; 
lean_dec_ref_known(v___x_1505_, 1);
v___x_1506_ = l_Lean_IR_Checker_checkArg(v_y_1503_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_dec_ref_known(v___x_1506_, 1);
v_fnBody_1444_ = v_b_1504_;
goto _start;
}
else
{
lean_dec(v_b_1504_);
lean_dec_ref(v_a_1445_);
return v___x_1506_;
}
}
else
{
lean_dec(v_b_1504_);
lean_dec(v_y_1503_);
lean_dec_ref(v_a_1445_);
return v___x_1505_;
}
}
case 3:
{
lean_object* v_x_1508_; lean_object* v_b_1509_; lean_object* v___x_1510_; 
v_x_1508_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_x_1508_);
v_b_1509_ = lean_ctor_get(v_fnBody_1444_, 2);
lean_inc(v_b_1509_);
lean_dec_ref_known(v_fnBody_1444_, 3);
v___x_1510_ = l_Lean_IR_Checker_checkVar(v_x_1508_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec_ref_known(v___x_1510_, 1);
v_fnBody_1444_ = v_b_1509_;
goto _start;
}
else
{
lean_dec(v_b_1509_);
lean_dec_ref(v_a_1445_);
return v___x_1510_;
}
}
case 4:
{
lean_object* v_x_1512_; lean_object* v_y_1513_; lean_object* v_b_1514_; lean_object* v___x_1515_; 
v_x_1512_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_x_1512_);
v_y_1513_ = lean_ctor_get(v_fnBody_1444_, 2);
lean_inc(v_y_1513_);
v_b_1514_ = lean_ctor_get(v_fnBody_1444_, 3);
lean_inc(v_b_1514_);
lean_dec_ref_known(v_fnBody_1444_, 4);
v___x_1515_ = l_Lean_IR_Checker_checkVar(v_x_1512_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; 
lean_dec_ref_known(v___x_1515_, 1);
v___x_1516_ = l_Lean_IR_Checker_checkVar(v_y_1513_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_dec_ref_known(v___x_1516_, 1);
v_fnBody_1444_ = v_b_1514_;
goto _start;
}
else
{
lean_dec(v_b_1514_);
lean_dec_ref(v_a_1445_);
return v___x_1516_;
}
}
else
{
lean_dec(v_b_1514_);
lean_dec(v_y_1513_);
lean_dec_ref(v_a_1445_);
return v___x_1515_;
}
}
case 5:
{
lean_object* v_x_1518_; lean_object* v_y_1519_; lean_object* v_b_1520_; lean_object* v___x_1521_; 
v_x_1518_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_x_1518_);
v_y_1519_ = lean_ctor_get(v_fnBody_1444_, 3);
lean_inc(v_y_1519_);
v_b_1520_ = lean_ctor_get(v_fnBody_1444_, 5);
lean_inc(v_b_1520_);
lean_dec_ref_known(v_fnBody_1444_, 6);
v___x_1521_ = l_Lean_IR_Checker_checkVar(v_x_1518_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref_known(v___x_1521_, 1);
v___x_1522_ = l_Lean_IR_Checker_checkVar(v_y_1519_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_dec_ref_known(v___x_1522_, 1);
v_fnBody_1444_ = v_b_1520_;
goto _start;
}
else
{
lean_dec(v_b_1520_);
lean_dec_ref(v_a_1445_);
return v___x_1522_;
}
}
else
{
lean_dec(v_b_1520_);
lean_dec(v_y_1519_);
lean_dec_ref(v_a_1445_);
return v___x_1521_;
}
}
case 8:
{
lean_object* v_x_1524_; lean_object* v_b_1525_; lean_object* v___x_1526_; 
v_x_1524_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_x_1524_);
v_b_1525_ = lean_ctor_get(v_fnBody_1444_, 1);
lean_inc(v_b_1525_);
lean_dec_ref_known(v_fnBody_1444_, 2);
v___x_1526_ = l_Lean_IR_Checker_checkVar(v_x_1524_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_dec_ref_known(v___x_1526_, 1);
v_fnBody_1444_ = v_b_1525_;
goto _start;
}
else
{
lean_dec(v_b_1525_);
lean_dec_ref(v_a_1445_);
return v___x_1526_;
}
}
case 9:
{
lean_object* v_x_1528_; lean_object* v_cs_1529_; lean_object* v___x_1530_; 
v_x_1528_ = lean_ctor_get(v_fnBody_1444_, 1);
lean_inc(v_x_1528_);
v_cs_1529_ = lean_ctor_get(v_fnBody_1444_, 3);
lean_inc_ref(v_cs_1529_);
lean_dec_ref_known(v_fnBody_1444_, 4);
v___x_1530_ = l_Lean_IR_Checker_checkVar(v_x_1528_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1551_; 
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v___x_1530_, 0);
lean_dec(v_unused_1552_);
v___x_1532_ = v___x_1530_;
v_isShared_1533_ = v_isSharedCheck_1551_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v___x_1530_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1551_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_array_get_size(v_cs_1529_);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_nat_dec_lt(v___x_1534_, v___x_1535_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1539_; 
lean_dec_ref(v_cs_1529_);
lean_dec_ref(v_a_1445_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1536_);
v___x_1539_ = v___x_1532_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1536_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
else
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_nat_dec_le(v___x_1535_, v___x_1535_);
if (v___x_1541_ == 0)
{
if (v___x_1537_ == 0)
{
lean_object* v___x_1543_; 
lean_dec_ref(v_cs_1529_);
lean_dec_ref(v_a_1445_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1536_);
v___x_1543_ = v___x_1532_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1536_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
lean_del_object(v___x_1532_);
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = lean_usize_of_nat(v___x_1535_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1529_, v___x_1545_, v___x_1546_, v___x_1536_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec_ref(v_a_1445_);
lean_dec_ref(v_cs_1529_);
return v___x_1547_;
}
}
else
{
size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
lean_del_object(v___x_1532_);
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = lean_usize_of_nat(v___x_1535_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1529_, v___x_1548_, v___x_1549_, v___x_1536_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec_ref(v_a_1445_);
lean_dec_ref(v_cs_1529_);
return v___x_1550_;
}
}
}
}
else
{
lean_dec_ref(v_cs_1529_);
lean_dec_ref(v_a_1445_);
return v___x_1530_;
}
}
case 10:
{
lean_object* v_x_1553_; lean_object* v___x_1554_; 
v_x_1553_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_x_1553_);
lean_dec_ref_known(v_fnBody_1444_, 1);
v___x_1554_ = l_Lean_IR_Checker_checkArg(v_x_1553_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec_ref(v_a_1445_);
return v___x_1554_;
}
case 11:
{
lean_object* v_j_1555_; lean_object* v_ys_1556_; lean_object* v___x_1557_; 
v_j_1555_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_j_1555_);
v_ys_1556_ = lean_ctor_get(v_fnBody_1444_, 1);
lean_inc_ref(v_ys_1556_);
lean_dec_ref_known(v_fnBody_1444_, 2);
v___x_1557_ = l_Lean_IR_Checker_checkJP(v_j_1555_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; 
lean_dec_ref_known(v___x_1557_, 1);
v___x_1558_ = l_Lean_IR_Checker_checkArgs(v_ys_1556_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec_ref(v_a_1445_);
lean_dec_ref(v_ys_1556_);
return v___x_1558_;
}
else
{
lean_dec_ref(v_ys_1556_);
lean_dec_ref(v_a_1445_);
return v___x_1557_;
}
}
case 12:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec_ref(v_a_1445_);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
default: 
{
lean_object* v_x_1561_; lean_object* v_b_1562_; 
v_x_1561_ = lean_ctor_get(v_fnBody_1444_, 0);
lean_inc(v_x_1561_);
v_b_1562_ = lean_ctor_get(v_fnBody_1444_, 2);
lean_inc(v_b_1562_);
lean_dec(v_fnBody_1444_);
v_x_1451_ = v_x_1561_;
v_b_1452_ = v_b_1562_;
v___y_1453_ = v_a_1445_;
v___y_1454_ = v_a_1446_;
v___y_1455_ = v_a_1447_;
v___y_1456_ = v_a_1448_;
goto v___jp_1450_;
}
}
v___jp_1450_:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_IR_Checker_checkVar(v_x_1451_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_dec_ref_known(v___x_1457_, 1);
v_fnBody_1444_ = v_b_1452_;
v_a_1445_ = v___y_1453_;
v_a_1446_ = v___y_1454_;
v_a_1447_ = v___y_1455_;
v_a_1448_ = v___y_1456_;
goto _start;
}
else
{
lean_dec_ref(v___y_1453_);
lean_dec(v_b_1452_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1563_, size_t v_i_1564_, size_t v_stop_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_usize_dec_eq(v_i_1564_, v_stop_1565_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_array_uget_borrowed(v_as_1563_, v_i_1564_);
v___x_1574_ = l_Lean_IR_Alt_body(v___x_1573_);
lean_inc_ref(v___y_1567_);
v___x_1575_ = l_Lean_IR_Checker_checkFnBody(v___x_1574_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; size_t v___x_1577_; size_t v___x_1578_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = ((size_t)1ULL);
v___x_1578_ = lean_usize_add(v_i_1564_, v___x_1577_);
v_i_1564_ = v___x_1578_;
v_b_1566_ = v_a_1576_;
goto _start;
}
else
{
return v___x_1575_;
}
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_b_1566_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1581_, lean_object* v_i_1582_, lean_object* v_stop_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
size_t v_i_boxed_1590_; size_t v_stop_boxed_1591_; lean_object* v_res_1592_; 
v_i_boxed_1590_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_stop_boxed_1591_ = lean_unbox_usize(v_stop_1583_);
lean_dec(v_stop_1583_);
v_res_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1581_, v_i_boxed_1590_, v_stop_boxed_1591_, v_b_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_as_1581_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 0)
{
lean_object* v_xs_1606_; lean_object* v_body_1607_; lean_object* v_localCtx_1608_; lean_object* v_currentDecl_1609_; lean_object* v_decls_1610_; lean_object* v_a_1612_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_xs_1606_ = lean_ctor_get(v_x_1600_, 1);
lean_inc_ref(v_xs_1606_);
v_body_1607_ = lean_ctor_get(v_x_1600_, 3);
lean_inc(v_body_1607_);
lean_dec_ref_known(v_x_1600_, 5);
v_localCtx_1608_ = lean_ctor_get(v_a_1601_, 0);
v_currentDecl_1609_ = lean_ctor_get(v_a_1601_, 1);
v_decls_1610_ = lean_ctor_get(v_a_1601_, 2);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_array_get_size(v_xs_1606_);
v___x_1617_ = lean_nat_dec_lt(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_dec_ref(v_xs_1606_);
lean_inc(v_localCtx_1608_);
v_a_1612_ = v_localCtx_1608_;
goto v___jp_1611_;
}
else
{
size_t v___x_1618_; size_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = ((size_t)0ULL);
v___x_1619_ = lean_usize_of_nat(v___x_1616_);
lean_inc(v_localCtx_1608_);
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1606_, v___x_1618_, v___x_1619_, v_localCtx_1608_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec_ref(v_xs_1606_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v_a_1612_ = v_a_1621_;
goto v___jp_1611_;
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_body_1607_);
v_a_1622_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1620_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
v___jp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_inc_ref(v_decls_1610_);
lean_inc_ref(v_currentDecl_1609_);
v___x_1613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1613_, 0, v_a_1612_);
lean_ctor_set(v___x_1613_, 1, v_currentDecl_1609_);
lean_ctor_set(v___x_1613_, 2, v_decls_1610_);
v___x_1614_ = l_Lean_IR_Checker_checkFnBody(v_body_1607_, v___x_1613_, v_a_1602_, v_a_1603_, v_a_1604_);
return v___x_1614_;
}
}
else
{
lean_object* v_xs_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v_xs_1630_ = lean_ctor_get(v_x_1600_, 1);
lean_inc_ref(v_xs_1630_);
lean_dec_ref_known(v_x_1600_, 4);
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_array_get_size(v_xs_1630_);
v___x_1634_ = lean_nat_dec_lt(v___x_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref(v_xs_1630_);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1631_);
return v___x_1635_;
}
else
{
lean_object* v_localCtx_1636_; size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
v_localCtx_1636_ = lean_ctor_get(v_a_1601_, 0);
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = lean_usize_of_nat(v___x_1633_);
lean_inc(v_localCtx_1636_);
v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1630_, v___x_1637_, v___x_1638_, v_localCtx_1636_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec_ref(v_xs_1630_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v___x_1639_, 0);
lean_dec(v_unused_1647_);
v___x_1641_ = v___x_1639_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v___x_1639_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1631_);
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1631_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1639_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1639_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_IR_Checker_checkDecl(v_x_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_1663_, lean_object* v_decl_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1668_ = lean_box(1);
lean_inc_ref(v_decl_1664_);
v___x_1669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v_decl_1664_);
lean_ctor_set(v___x_1669_, 2, v_decls_1663_);
v___x_1670_ = lean_st_mk_ref(v___x_1668_);
v___x_1671_ = l_Lean_IR_Checker_checkDecl(v_decl_1664_, v___x_1669_, v___x_1670_, v_a_1665_, v_a_1666_);
lean_dec_ref_known(v___x_1669_, 3);
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
uint8_t v___x_1723_; 
v___x_1723_ = lean_nat_dec_le(v___x_1719_, v___x_1719_);
if (v___x_1723_ == 0)
{
if (v___x_1721_ == 0)
{
lean_object* v___x_1724_; 
lean_dec_ref(v_decls_1714_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1720_);
return v___x_1724_;
}
else
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = lean_usize_of_nat(v___x_1719_);
lean_inc_ref(v_decls_1714_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1714_, v_decls_1714_, v___x_1725_, v___x_1726_, v___x_1720_, v_a_1715_, v_a_1716_);
lean_dec_ref(v_decls_1714_);
return v___x_1727_;
}
}
else
{
size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = ((size_t)0ULL);
v___x_1729_ = lean_usize_of_nat(v___x_1719_);
lean_inc_ref(v_decls_1714_);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1714_, v_decls_1714_, v___x_1728_, v___x_1729_, v___x_1720_, v_a_1715_, v_a_1716_);
lean_dec_ref(v_decls_1714_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_IR_checkDecls(v_decls_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
return v_res_1735_;
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
