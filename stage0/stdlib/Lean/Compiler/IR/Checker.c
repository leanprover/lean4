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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_24_; lean_object* v_toCold_25_; lean_object* v_env_26_; lean_object* v_options_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_toCold_25_ = lean_ctor_get(v___y_21_, 0);
v_env_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_24_);
v_options_27_ = lean_ctor_get(v_toCold_25_, 2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2);
v___x_29_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_27_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_env_26_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
lean_ctor_set(v___x_30_, 3, v_options_27_);
v___x_31_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v_msgData_20_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object* v_msgData_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msgData_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object* v_msg_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_ref_42_; lean_object* v___x_43_; lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_ref_42_ = lean_ctor_get(v___y_39_, 2);
v___x_43_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msg_38_, v___y_39_, v___y_40_);
v_a_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_52_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
lean_inc(v_ref_42_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v_ref_42_);
lean_ctor_set(v___x_48_, 1, v_a_44_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 1);
lean_ctor_set(v___x_46_, 0, v___x_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_48_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object* v_msg_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_57_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0));
v___x_60_ = l_Lean_stringToMessageData(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__2));
v___x_63_ = l_Lean_stringToMessageData(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object* v_msg_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_currentDecl_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_currentDecl_70_ = lean_ctor_get(v_a_65_, 1);
v___x_71_ = l_Lean_IR_Decl_name(v_currentDecl_70_);
v___x_72_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__1, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1);
v___x_73_ = 0;
v___x_74_ = l_Lean_MessageData_ofConstName(v___x_71_, v___x_73_);
v___x_75_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_72_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__3, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3);
v___x_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = l_Lean_stringToMessageData(v_msg_64_);
v___x_79_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v___x_79_, v_a_67_, v_a_68_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object* v_msg_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object* v_00_u03b1_88_, lean_object* v_msg_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object* v_00_u03b1_96_, lean_object* v_msg_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_IR_Checker_throwCheckerError(v_00_u03b1_96_, v_msg_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object* v_00_u03b1_104_, lean_object* v_msg_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_105_, v___y_108_, v___y_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object* v_00_u03b1_112_, lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(v_00_u03b1_112_, v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object* v_k_120_, lean_object* v_v_121_, lean_object* v_t_122_){
_start:
{
if (lean_obj_tag(v_t_122_) == 0)
{
lean_object* v_size_123_; lean_object* v_k_124_; lean_object* v_v_125_; lean_object* v_l_126_; lean_object* v_r_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_408_; 
v_size_123_ = lean_ctor_get(v_t_122_, 0);
v_k_124_ = lean_ctor_get(v_t_122_, 1);
v_v_125_ = lean_ctor_get(v_t_122_, 2);
v_l_126_ = lean_ctor_get(v_t_122_, 3);
v_r_127_ = lean_ctor_get(v_t_122_, 4);
v_isSharedCheck_408_ = !lean_is_exclusive(v_t_122_);
if (v_isSharedCheck_408_ == 0)
{
v___x_129_ = v_t_122_;
v_isShared_130_ = v_isSharedCheck_408_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_r_127_);
lean_inc(v_l_126_);
lean_inc(v_v_125_);
lean_inc(v_k_124_);
lean_inc(v_size_123_);
lean_dec(v_t_122_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_408_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_lt(v_k_120_, v_k_124_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_eq(v_k_120_, v_k_124_);
if (v___x_132_ == 0)
{
lean_object* v_impl_133_; lean_object* v___x_134_; 
lean_dec(v_size_123_);
v_impl_133_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_120_, v_v_121_, v_r_127_);
v___x_134_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_126_) == 0)
{
lean_object* v_size_135_; lean_object* v_size_136_; lean_object* v_k_137_; lean_object* v_v_138_; lean_object* v_l_139_; lean_object* v_r_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_size_135_ = lean_ctor_get(v_l_126_, 0);
v_size_136_ = lean_ctor_get(v_impl_133_, 0);
lean_inc(v_size_136_);
v_k_137_ = lean_ctor_get(v_impl_133_, 1);
lean_inc(v_k_137_);
v_v_138_ = lean_ctor_get(v_impl_133_, 2);
lean_inc(v_v_138_);
v_l_139_ = lean_ctor_get(v_impl_133_, 3);
lean_inc(v_l_139_);
v_r_140_ = lean_ctor_get(v_impl_133_, 4);
lean_inc(v_r_140_);
v___x_141_ = lean_unsigned_to_nat(3u);
v___x_142_ = lean_nat_mul(v___x_141_, v_size_135_);
v___x_143_ = lean_nat_dec_lt(v___x_142_, v_size_136_);
lean_dec(v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
lean_dec(v_r_140_);
lean_dec(v_l_139_);
lean_dec(v_v_138_);
lean_dec(v_k_137_);
v___x_144_ = lean_nat_add(v___x_134_, v_size_135_);
v___x_145_ = lean_nat_add(v___x_144_, v_size_136_);
lean_dec(v_size_136_);
lean_dec(v___x_144_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_impl_133_);
lean_ctor_set(v___x_129_, 0, v___x_145_);
v___x_147_ = v___x_129_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_impl_133_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
else
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_212_; 
v_isSharedCheck_212_ = !lean_is_exclusive(v_impl_133_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; lean_object* v_unused_217_; 
v_unused_213_ = lean_ctor_get(v_impl_133_, 4);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_impl_133_, 3);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_impl_133_, 2);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_impl_133_, 1);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_impl_133_, 0);
lean_dec(v_unused_217_);
v___x_150_ = v_impl_133_;
v_isShared_151_ = v_isSharedCheck_212_;
goto v_resetjp_149_;
}
else
{
lean_dec(v_impl_133_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_212_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v_size_152_; lean_object* v_k_153_; lean_object* v_v_154_; lean_object* v_l_155_; lean_object* v_r_156_; lean_object* v_size_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_size_152_ = lean_ctor_get(v_l_139_, 0);
v_k_153_ = lean_ctor_get(v_l_139_, 1);
v_v_154_ = lean_ctor_get(v_l_139_, 2);
v_l_155_ = lean_ctor_get(v_l_139_, 3);
v_r_156_ = lean_ctor_get(v_l_139_, 4);
v_size_157_ = lean_ctor_get(v_r_140_, 0);
v___x_158_ = lean_unsigned_to_nat(2u);
v___x_159_ = lean_nat_mul(v___x_158_, v_size_157_);
v___x_160_ = lean_nat_dec_lt(v_size_152_, v___x_159_);
lean_dec(v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_188_; 
lean_inc(v_r_156_);
lean_inc(v_l_155_);
lean_inc(v_v_154_);
lean_inc(v_k_153_);
v_isSharedCheck_188_ = !lean_is_exclusive(v_l_139_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; lean_object* v_unused_193_; 
v_unused_189_ = lean_ctor_get(v_l_139_, 4);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_l_139_, 3);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_l_139_, 2);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_l_139_, 1);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_l_139_, 0);
lean_dec(v_unused_193_);
v___x_162_ = v_l_139_;
v_isShared_163_ = v_isSharedCheck_188_;
goto v_resetjp_161_;
}
else
{
lean_dec(v_l_139_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_188_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_178_; 
v___x_164_ = lean_nat_add(v___x_134_, v_size_135_);
v___x_165_ = lean_nat_add(v___x_164_, v_size_136_);
lean_dec(v_size_136_);
if (lean_obj_tag(v_l_155_) == 0)
{
lean_object* v_size_186_; 
v_size_186_ = lean_ctor_get(v_l_155_, 0);
lean_inc(v_size_186_);
v___y_178_ = v_size_186_;
goto v___jp_177_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___y_178_ = v___x_187_;
goto v___jp_177_;
}
v___jp_166_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_nat_add(v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec(v___y_168_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 4, v_r_140_);
lean_ctor_set(v___x_162_, 3, v_r_156_);
lean_ctor_set(v___x_162_, 2, v_v_138_);
lean_ctor_set(v___x_162_, 1, v_k_137_);
lean_ctor_set(v___x_162_, 0, v___x_170_);
v___x_172_ = v___x_162_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_k_137_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_v_138_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_r_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_r_140_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 4, v___x_172_);
lean_ctor_set(v___x_150_, 3, v___y_167_);
lean_ctor_set(v___x_150_, 2, v_v_154_);
lean_ctor_set(v___x_150_, 1, v_k_153_);
lean_ctor_set(v___x_150_, 0, v___x_165_);
v___x_174_ = v___x_150_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_153_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_154_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v___y_167_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_nat_add(v___x_164_, v___y_178_);
lean_dec(v___y_178_);
lean_dec(v___x_164_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_l_155_);
lean_ctor_set(v___x_129_, 0, v___x_179_);
v___x_181_ = v___x_129_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v_l_155_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = lean_nat_add(v___x_134_, v_size_157_);
if (lean_obj_tag(v_r_156_) == 0)
{
lean_object* v_size_183_; 
v_size_183_ = lean_ctor_get(v_r_156_, 0);
lean_inc(v_size_183_);
v___y_167_ = v___x_181_;
v___y_168_ = v___x_182_;
v___y_169_ = v_size_183_;
goto v___jp_166_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___y_167_ = v___x_181_;
v___y_168_ = v___x_182_;
v___y_169_ = v___x_184_;
goto v___jp_166_;
}
}
}
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
lean_del_object(v___x_129_);
v___x_194_ = lean_nat_add(v___x_134_, v_size_135_);
v___x_195_ = lean_nat_add(v___x_194_, v_size_136_);
lean_dec(v_size_136_);
v___x_196_ = lean_nat_add(v___x_194_, v_size_152_);
lean_dec(v___x_194_);
lean_inc_ref(v_l_126_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 4, v_l_139_);
lean_ctor_set(v___x_150_, 3, v_l_126_);
lean_ctor_set(v___x_150_, 2, v_v_125_);
lean_ctor_set(v___x_150_, 1, v_k_124_);
lean_ctor_set(v___x_150_, 0, v___x_196_);
v___x_198_ = v___x_150_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v_l_139_);
v___x_198_ = v_reuseFailAlloc_211_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_isSharedCheck_205_ = !lean_is_exclusive(v_l_126_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; 
v_unused_206_ = lean_ctor_get(v_l_126_, 4);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_l_126_, 3);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_l_126_, 2);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_l_126_, 1);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_l_126_, 0);
lean_dec(v_unused_210_);
v___x_200_ = v_l_126_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_dec(v_l_126_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 4, v_r_140_);
lean_ctor_set(v___x_200_, 3, v___x_198_);
lean_ctor_set(v___x_200_, 2, v_v_138_);
lean_ctor_set(v___x_200_, 1, v_k_137_);
lean_ctor_set(v___x_200_, 0, v___x_195_);
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_k_137_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_v_138_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_r_140_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_218_; 
v_l_218_ = lean_ctor_get(v_impl_133_, 3);
lean_inc(v_l_218_);
if (lean_obj_tag(v_l_218_) == 0)
{
lean_object* v_r_219_; lean_object* v_k_220_; lean_object* v_v_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_244_; 
v_r_219_ = lean_ctor_get(v_impl_133_, 4);
v_k_220_ = lean_ctor_get(v_impl_133_, 1);
v_v_221_ = lean_ctor_get(v_impl_133_, 2);
v_isSharedCheck_244_ = !lean_is_exclusive(v_impl_133_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_245_ = lean_ctor_get(v_impl_133_, 3);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_impl_133_, 0);
lean_dec(v_unused_246_);
v___x_223_ = v_impl_133_;
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_r_219_);
lean_inc(v_v_221_);
lean_inc(v_k_220_);
lean_dec(v_impl_133_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_k_225_; lean_object* v_v_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_240_; 
v_k_225_ = lean_ctor_get(v_l_218_, 1);
v_v_226_ = lean_ctor_get(v_l_218_, 2);
v_isSharedCheck_240_ = !lean_is_exclusive(v_l_218_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; lean_object* v_unused_242_; lean_object* v_unused_243_; 
v_unused_241_ = lean_ctor_get(v_l_218_, 4);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_l_218_, 3);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_l_218_, 0);
lean_dec(v_unused_243_);
v___x_228_ = v_l_218_;
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_v_226_);
lean_inc(v_k_225_);
lean_dec(v_l_218_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_219_, 2);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 4, v_r_219_);
lean_ctor_set(v___x_228_, 3, v_r_219_);
lean_ctor_set(v___x_228_, 2, v_v_125_);
lean_ctor_set(v___x_228_, 1, v_k_124_);
lean_ctor_set(v___x_228_, 0, v___x_134_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_r_219_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_r_219_);
v___x_232_ = v_reuseFailAlloc_239_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
lean_inc(v_r_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 3, v_r_219_);
lean_ctor_set(v___x_223_, 0, v___x_134_);
v___x_234_ = v___x_223_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_k_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_v_221_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_r_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_r_219_);
v___x_234_ = v_reuseFailAlloc_238_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_234_);
lean_ctor_set(v___x_129_, 3, v___x_232_);
lean_ctor_set(v___x_129_, 2, v_v_226_);
lean_ctor_set(v___x_129_, 1, v_k_225_);
lean_ctor_set(v___x_129_, 0, v___x_230_);
v___x_236_ = v___x_129_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_k_225_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_v_226_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
}
else
{
lean_object* v_r_247_; 
v_r_247_ = lean_ctor_get(v_impl_133_, 4);
lean_inc(v_r_247_);
if (lean_obj_tag(v_r_247_) == 0)
{
lean_object* v_k_248_; lean_object* v_v_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_260_; 
v_k_248_ = lean_ctor_get(v_impl_133_, 1);
v_v_249_ = lean_ctor_get(v_impl_133_, 2);
v_isSharedCheck_260_ = !lean_is_exclusive(v_impl_133_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_261_ = lean_ctor_get(v_impl_133_, 4);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_impl_133_, 3);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_impl_133_, 0);
lean_dec(v_unused_263_);
v___x_251_ = v_impl_133_;
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_v_249_);
lean_inc(v_k_248_);
lean_dec(v_impl_133_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_unsigned_to_nat(3u);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 4, v_l_218_);
lean_ctor_set(v___x_251_, 2, v_v_125_);
lean_ctor_set(v___x_251_, 1, v_k_124_);
lean_ctor_set(v___x_251_, 0, v___x_134_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_l_218_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_l_218_);
v___x_255_ = v_reuseFailAlloc_259_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_r_247_);
lean_ctor_set(v___x_129_, 3, v___x_255_);
lean_ctor_set(v___x_129_, 2, v_v_249_);
lean_ctor_set(v___x_129_, 1, v_k_248_);
lean_ctor_set(v___x_129_, 0, v___x_253_);
v___x_257_ = v___x_129_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_248_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_249_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_r_247_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_unsigned_to_nat(2u);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_impl_133_);
lean_ctor_set(v___x_129_, 3, v_r_247_);
lean_ctor_set(v___x_129_, 0, v___x_264_);
v___x_266_ = v___x_129_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_267_, 3, v_r_247_);
lean_ctor_set(v_reuseFailAlloc_267_, 4, v_impl_133_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
else
{
lean_object* v___x_269_; 
lean_dec(v_v_125_);
lean_dec(v_k_124_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v_v_121_);
lean_ctor_set(v___x_129_, 1, v_k_120_);
v___x_269_ = v___x_129_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_size_123_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v_r_127_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v_impl_271_; lean_object* v___x_272_; 
lean_dec(v_size_123_);
v_impl_271_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_120_, v_v_121_, v_l_126_);
v___x_272_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_127_) == 0)
{
lean_object* v_size_273_; lean_object* v_size_274_; lean_object* v_k_275_; lean_object* v_v_276_; lean_object* v_l_277_; lean_object* v_r_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_size_273_ = lean_ctor_get(v_r_127_, 0);
v_size_274_ = lean_ctor_get(v_impl_271_, 0);
lean_inc(v_size_274_);
v_k_275_ = lean_ctor_get(v_impl_271_, 1);
lean_inc(v_k_275_);
v_v_276_ = lean_ctor_get(v_impl_271_, 2);
lean_inc(v_v_276_);
v_l_277_ = lean_ctor_get(v_impl_271_, 3);
lean_inc(v_l_277_);
v_r_278_ = lean_ctor_get(v_impl_271_, 4);
lean_inc(v_r_278_);
v___x_279_ = lean_unsigned_to_nat(3u);
v___x_280_ = lean_nat_mul(v___x_279_, v_size_273_);
v___x_281_ = lean_nat_dec_lt(v___x_280_, v_size_274_);
lean_dec(v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
lean_dec(v_r_278_);
lean_dec(v_l_277_);
lean_dec(v_v_276_);
lean_dec(v_k_275_);
v___x_282_ = lean_nat_add(v___x_272_, v_size_274_);
lean_dec(v_size_274_);
v___x_283_ = lean_nat_add(v___x_282_, v_size_273_);
lean_dec(v___x_282_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 3, v_impl_271_);
lean_ctor_set(v___x_129_, 0, v___x_283_);
v___x_285_ = v___x_129_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_impl_271_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_r_127_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
else
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_352_; 
v_isSharedCheck_352_ = !lean_is_exclusive(v_impl_271_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; 
v_unused_353_ = lean_ctor_get(v_impl_271_, 4);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_impl_271_, 3);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_impl_271_, 2);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_impl_271_, 1);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_impl_271_, 0);
lean_dec(v_unused_357_);
v___x_288_ = v_impl_271_;
v_isShared_289_ = v_isSharedCheck_352_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_impl_271_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_352_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_size_290_; lean_object* v_size_291_; lean_object* v_k_292_; lean_object* v_v_293_; lean_object* v_l_294_; lean_object* v_r_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_size_290_ = lean_ctor_get(v_l_277_, 0);
v_size_291_ = lean_ctor_get(v_r_278_, 0);
v_k_292_ = lean_ctor_get(v_r_278_, 1);
v_v_293_ = lean_ctor_get(v_r_278_, 2);
v_l_294_ = lean_ctor_get(v_r_278_, 3);
v_r_295_ = lean_ctor_get(v_r_278_, 4);
v___x_296_ = lean_unsigned_to_nat(2u);
v___x_297_ = lean_nat_mul(v___x_296_, v_size_290_);
v___x_298_ = lean_nat_dec_lt(v_size_291_, v___x_297_);
lean_dec(v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_327_; 
lean_inc(v_r_295_);
lean_inc(v_l_294_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
v_isSharedCheck_327_ = !lean_is_exclusive(v_r_278_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_328_ = lean_ctor_get(v_r_278_, 4);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_r_278_, 3);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_r_278_, 2);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_r_278_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_r_278_, 0);
lean_dec(v_unused_332_);
v___x_300_ = v_r_278_;
v_isShared_301_ = v_isSharedCheck_327_;
goto v_resetjp_299_;
}
else
{
lean_dec(v_r_278_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_327_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___x_315_; lean_object* v___y_317_; 
v___x_302_ = lean_nat_add(v___x_272_, v_size_274_);
lean_dec(v_size_274_);
v___x_303_ = lean_nat_add(v___x_302_, v_size_273_);
lean_dec(v___x_302_);
v___x_315_ = lean_nat_add(v___x_272_, v_size_290_);
if (lean_obj_tag(v_l_294_) == 0)
{
lean_object* v_size_325_; 
v_size_325_ = lean_ctor_get(v_l_294_, 0);
lean_inc(v_size_325_);
v___y_317_ = v_size_325_;
goto v___jp_316_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___y_317_ = v___x_326_;
goto v___jp_316_;
}
v___jp_304_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_308_ = lean_nat_add(v___y_305_, v___y_307_);
lean_dec(v___y_307_);
lean_dec(v___y_305_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v_r_127_);
lean_ctor_set(v___x_300_, 3, v_r_295_);
lean_ctor_set(v___x_300_, 2, v_v_125_);
lean_ctor_set(v___x_300_, 1, v_k_124_);
lean_ctor_set(v___x_300_, 0, v___x_308_);
v___x_310_ = v___x_300_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v_r_295_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v_r_127_);
v___x_310_ = v_reuseFailAlloc_314_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_312_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 4, v___x_310_);
lean_ctor_set(v___x_288_, 3, v___y_306_);
lean_ctor_set(v___x_288_, 2, v_v_293_);
lean_ctor_set(v___x_288_, 1, v_k_292_);
lean_ctor_set(v___x_288_, 0, v___x_303_);
v___x_312_ = v___x_288_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_k_292_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_v_293_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v___y_306_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
v___jp_316_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_nat_add(v___x_315_, v___y_317_);
lean_dec(v___y_317_);
lean_dec(v___x_315_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_l_294_);
lean_ctor_set(v___x_129_, 3, v_l_277_);
lean_ctor_set(v___x_129_, 2, v_v_276_);
lean_ctor_set(v___x_129_, 1, v_k_275_);
lean_ctor_set(v___x_129_, 0, v___x_318_);
v___x_320_ = v___x_129_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_l_277_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v_l_294_);
v___x_320_ = v_reuseFailAlloc_324_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; 
v___x_321_ = lean_nat_add(v___x_272_, v_size_273_);
if (lean_obj_tag(v_r_295_) == 0)
{
lean_object* v_size_322_; 
v_size_322_ = lean_ctor_get(v_r_295_, 0);
lean_inc(v_size_322_);
v___y_305_ = v___x_321_;
v___y_306_ = v___x_320_;
v___y_307_ = v_size_322_;
goto v___jp_304_;
}
else
{
lean_object* v___x_323_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___y_305_ = v___x_321_;
v___y_306_ = v___x_320_;
v___y_307_ = v___x_323_;
goto v___jp_304_;
}
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_del_object(v___x_129_);
v___x_333_ = lean_nat_add(v___x_272_, v_size_274_);
lean_dec(v_size_274_);
v___x_334_ = lean_nat_add(v___x_333_, v_size_273_);
lean_dec(v___x_333_);
v___x_335_ = lean_nat_add(v___x_272_, v_size_273_);
v___x_336_ = lean_nat_add(v___x_335_, v_size_291_);
lean_dec(v___x_335_);
lean_inc_ref(v_r_127_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 4, v_r_127_);
lean_ctor_set(v___x_288_, 3, v_r_278_);
lean_ctor_set(v___x_288_, 2, v_v_125_);
lean_ctor_set(v___x_288_, 1, v_k_124_);
lean_ctor_set(v___x_288_, 0, v___x_336_);
v___x_338_ = v___x_288_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_r_278_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_r_127_);
v___x_338_ = v_reuseFailAlloc_351_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_isSharedCheck_345_ = !lean_is_exclusive(v_r_127_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; lean_object* v_unused_350_; 
v_unused_346_ = lean_ctor_get(v_r_127_, 4);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_r_127_, 3);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_r_127_, 2);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_r_127_, 1);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_r_127_, 0);
lean_dec(v_unused_350_);
v___x_340_ = v_r_127_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_dec(v_r_127_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 4, v___x_338_);
lean_ctor_set(v___x_340_, 3, v_l_277_);
lean_ctor_set(v___x_340_, 2, v_v_276_);
lean_ctor_set(v___x_340_, 1, v_k_275_);
lean_ctor_set(v___x_340_, 0, v___x_334_);
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_l_277_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v___x_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_358_; 
v_l_358_ = lean_ctor_get(v_impl_271_, 3);
lean_inc(v_l_358_);
if (lean_obj_tag(v_l_358_) == 0)
{
lean_object* v_r_359_; lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_372_; 
v_r_359_ = lean_ctor_get(v_impl_271_, 4);
v_k_360_ = lean_ctor_get(v_impl_271_, 1);
v_v_361_ = lean_ctor_get(v_impl_271_, 2);
v_isSharedCheck_372_ = !lean_is_exclusive(v_impl_271_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_373_ = lean_ctor_get(v_impl_271_, 3);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_impl_271_, 0);
lean_dec(v_unused_374_);
v___x_363_ = v_impl_271_;
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_r_359_);
lean_inc(v_v_361_);
lean_inc(v_k_360_);
lean_dec(v_impl_271_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_359_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 3, v_r_359_);
lean_ctor_set(v___x_363_, 2, v_v_125_);
lean_ctor_set(v___x_363_, 1, v_k_124_);
lean_ctor_set(v___x_363_, 0, v___x_272_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_r_359_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_r_359_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_367_);
lean_ctor_set(v___x_129_, 3, v_l_358_);
lean_ctor_set(v___x_129_, 2, v_v_361_);
lean_ctor_set(v___x_129_, 1, v_k_360_);
lean_ctor_set(v___x_129_, 0, v___x_365_);
v___x_369_ = v___x_129_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_l_358_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_r_375_; 
v_r_375_ = lean_ctor_get(v_impl_271_, 4);
lean_inc(v_r_375_);
if (lean_obj_tag(v_r_375_) == 0)
{
lean_object* v_k_376_; lean_object* v_v_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_400_; 
v_k_376_ = lean_ctor_get(v_impl_271_, 1);
v_v_377_ = lean_ctor_get(v_impl_271_, 2);
v_isSharedCheck_400_ = !lean_is_exclusive(v_impl_271_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; lean_object* v_unused_402_; lean_object* v_unused_403_; 
v_unused_401_ = lean_ctor_get(v_impl_271_, 4);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_impl_271_, 3);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_impl_271_, 0);
lean_dec(v_unused_403_);
v___x_379_ = v_impl_271_;
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_v_377_);
lean_inc(v_k_376_);
lean_dec(v_impl_271_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_k_381_; lean_object* v_v_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_396_; 
v_k_381_ = lean_ctor_get(v_r_375_, 1);
v_v_382_ = lean_ctor_get(v_r_375_, 2);
v_isSharedCheck_396_ = !lean_is_exclusive(v_r_375_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_397_ = lean_ctor_get(v_r_375_, 4);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_r_375_, 3);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_r_375_, 0);
lean_dec(v_unused_399_);
v___x_384_ = v_r_375_;
v_isShared_385_ = v_isSharedCheck_396_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_v_382_);
lean_inc(v_k_381_);
lean_dec(v_r_375_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_396_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_unsigned_to_nat(3u);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 4, v_l_358_);
lean_ctor_set(v___x_384_, 3, v_l_358_);
lean_ctor_set(v___x_384_, 2, v_v_377_);
lean_ctor_set(v___x_384_, 1, v_k_376_);
lean_ctor_set(v___x_384_, 0, v___x_272_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_k_376_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_v_377_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_l_358_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_l_358_);
v___x_388_ = v_reuseFailAlloc_395_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v_l_358_);
lean_ctor_set(v___x_379_, 2, v_v_125_);
lean_ctor_set(v___x_379_, 1, v_k_124_);
lean_ctor_set(v___x_379_, 0, v___x_272_);
v___x_390_ = v___x_379_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_l_358_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_l_358_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_390_);
lean_ctor_set(v___x_129_, 3, v___x_388_);
lean_ctor_set(v___x_129_, 2, v_v_382_);
lean_ctor_set(v___x_129_, 1, v_k_381_);
lean_ctor_set(v___x_129_, 0, v___x_386_);
v___x_392_ = v___x_129_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_k_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_v_382_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(2u);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_r_375_);
lean_ctor_set(v___x_129_, 3, v_impl_271_);
lean_ctor_set(v___x_129_, 0, v___x_404_);
v___x_406_ = v___x_129_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_impl_271_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_r_375_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_k_120_);
lean_ctor_set(v___x_410_, 2, v_v_121_);
lean_ctor_set(v___x_410_, 3, v_t_122_);
lean_ctor_set(v___x_410_, 4, v_t_122_);
return v___x_410_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* v_k_411_, lean_object* v_t_412_){
_start:
{
if (lean_obj_tag(v_t_412_) == 0)
{
lean_object* v_k_413_; lean_object* v_l_414_; lean_object* v_r_415_; uint8_t v___x_416_; 
v_k_413_ = lean_ctor_get(v_t_412_, 1);
v_l_414_ = lean_ctor_get(v_t_412_, 3);
v_r_415_ = lean_ctor_get(v_t_412_, 4);
v___x_416_ = lean_nat_dec_lt(v_k_411_, v_k_413_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
v___x_417_ = lean_nat_dec_eq(v_k_411_, v_k_413_);
if (v___x_417_ == 0)
{
v_t_412_ = v_r_415_;
goto _start;
}
else
{
return v___x_417_;
}
}
else
{
v_t_412_ = v_l_414_;
goto _start;
}
}
else
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* v_k_421_, lean_object* v_t_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_421_, v_t_422_);
lean_dec(v_t_422_);
lean_dec(v_k_421_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* v_i_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_440_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_st_ref_get(v_a_429_);
v___x_446_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_427_, v___x_445_);
lean_dec(v___x_445_);
if (v___x_446_ == 0)
{
v___y_440_ = v_a_429_;
goto v___jp_439_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_447_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__0));
v___x_448_ = l_Nat_reprFast(v_i_427_);
v___x_449_ = lean_string_append(v___x_447_, v___x_448_);
lean_dec_ref(v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__1));
v___x_451_ = lean_string_append(v___x_449_, v___x_450_);
v___x_452_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_451_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_452_;
}
v___jp_433_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_st_ref_put(v___y_434_, v___y_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___y_435_);
return v___x_438_;
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_st_ref_take(v___y_440_);
v___x_442_ = lean_box(0);
v___x_443_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_427_, v___x_441_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_i_427_, v___x_442_, v___x_441_);
v___y_434_ = v___y_440_;
v___y_435_ = v___x_442_;
v___y_436_ = v___x_444_;
goto v___jp_433_;
}
else
{
lean_dec(v_i_427_);
v___y_434_ = v___y_440_;
v___y_435_ = v___x_442_;
v___y_436_ = v___x_441_;
goto v___jp_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* v_i_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_IR_Checker_markIndex(v_i_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(lean_object* v_00_u03b2_460_, lean_object* v_k_461_, lean_object* v_t_462_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_461_, v_t_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* v_00_u03b2_464_, lean_object* v_k_465_, lean_object* v_t_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(v_00_u03b2_464_, v_k_465_, v_t_466_);
lean_dec(v_t_466_);
lean_dec(v_k_465_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(lean_object* v_00_u03b2_469_, lean_object* v_k_470_, lean_object* v_v_471_, lean_object* v_t_472_, lean_object* v_hl_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_470_, v_v_471_, v_t_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* v_x_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_IR_Checker_markIndex(v_x_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* v_x_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_IR_Checker_markVar(v_x_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* v_j_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_IR_Checker_markIndex(v_j_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* v_j_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_IR_Checker_markJP(v_j_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* v_c_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; lean_object* v_env_512_; lean_object* v_decls_513_; lean_object* v___x_514_; 
v___x_511_ = lean_st_ref_get(v_a_509_);
v_env_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc_ref(v_env_512_);
lean_dec(v___x_511_);
v_decls_513_ = lean_ctor_get(v_a_506_, 2);
lean_inc(v_c_505_);
v___x_514_ = l_Lean_IR_findEnvDecl_x27(v_env_512_, v_c_505_, v_decls_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_515_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
v___x_516_ = 1;
v___x_517_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_505_, v___x_516_);
v___x_518_ = lean_string_append(v___x_515_, v___x_517_);
lean_dec_ref(v___x_517_);
v___x_519_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
v___x_521_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_520_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_c_505_);
v_val_522_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_514_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_val_522_);
lean_dec(v___x_514_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_val_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* v_c_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_IR_Checker_getDecl(v_c_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* v_x_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
uint8_t v___y_547_; lean_object* v_localCtx_558_; uint8_t v___x_559_; 
v_localCtx_558_ = lean_ctor_get(v_a_541_, 0);
v___x_559_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_558_, v_x_540_);
if (v___x_559_ == 0)
{
uint8_t v___x_560_; 
v___x_560_ = l_Lean_IR_LocalContext_isParam(v_localCtx_558_, v_x_540_);
v___y_547_ = v___x_560_;
goto v___jp_546_;
}
else
{
v___y_547_ = v___x_559_;
goto v___jp_546_;
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_548_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_549_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_550_ = l_Nat_reprFast(v_x_540_);
v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = lean_string_append(v___x_548_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
v___x_555_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_554_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v_x_540_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_IR_Checker_checkVar(v_x_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_localCtx_576_; uint8_t v___x_577_; 
v_localCtx_576_ = lean_ctor_get(v_a_571_, 0);
v___x_577_ = l_Lean_IR_LocalContext_isJP(v_localCtx_576_, v_j_570_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_578_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_579_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_580_ = l_Nat_reprFast(v_j_570_);
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = lean_string_append(v___x_578_, v___x_581_);
lean_dec_ref(v___x_581_);
v___x_583_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
v___x_585_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_584_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_j_570_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_IR_Checker_checkJP(v_j_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
if (lean_obj_tag(v_a_595_) == 0)
{
lean_object* v_id_601_; lean_object* v___x_602_; 
v_id_601_ = lean_ctor_get(v_a_595_, 0);
lean_inc(v_id_601_);
lean_dec_ref_known(v_a_595_, 1);
v___x_602_ = l_Lean_IR_Checker_checkVar(v_id_601_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_IR_Checker_checkArg(v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_612_, size_t v_i_613_, size_t v_stop_614_, lean_object* v_b_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_eq(v_i_613_, v_stop_614_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_array_uget_borrowed(v_as_612_, v_i_613_);
lean_inc(v___x_622_);
v___x_623_ = l_Lean_IR_Checker_checkArg(v___x_622_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; size_t v___x_625_; size_t v___x_626_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_613_, v___x_625_);
v_i_613_ = v___x_626_;
v_b_615_ = v_a_624_;
goto _start;
}
else
{
return v___x_623_;
}
}
else
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_b_615_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_629_, lean_object* v_i_630_, lean_object* v_stop_631_, lean_object* v_b_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
size_t v_i_boxed_638_; size_t v_stop_boxed_639_; lean_object* v_res_640_; 
v_i_boxed_638_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_stop_boxed_639_ = lean_unbox_usize(v_stop_631_);
lean_dec(v_stop_631_);
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_629_, v_i_boxed_638_, v_stop_boxed_639_, v_b_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec_ref(v_as_629_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_array_get_size(v_as_641_);
v___x_649_ = lean_box(0);
v___x_650_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
return v___x_651_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_le(v___x_648_, v___x_648_);
if (v___x_652_ == 0)
{
if (v___x_650_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_649_);
return v___x_653_;
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_648_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_641_, v___x_654_, v___x_655_, v___x_649_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
return v___x_656_;
}
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = ((size_t)0ULL);
v___x_658_ = lean_usize_of_nat(v___x_648_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_641_, v___x_657_, v___x_658_, v___x_649_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_IR_Checker_checkArgs(v_as_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec_ref(v_as_660_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_668_, lean_object* v_ty_u2082_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_668_, v_ty_u2082_669_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_677_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_676_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_box(0);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_680_, lean_object* v_ty_u2082_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_680_, v_ty_u2082_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_ty_u2082_681_);
lean_dec(v_ty_u2081_680_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_690_, lean_object* v_p_691_, lean_object* v_suffix_x3f_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
lean_inc(v_ty_690_);
v___x_698_ = lean_apply_1(v_p_691_, v_ty_690_);
v___x_699_ = lean_unbox(v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_msg_707_; 
v___x_700_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_701_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_690_);
v___x_702_ = l_Std_Format_defWidth;
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = l_Std_Format_pretty(v___x_701_, v___x_702_, v___x_703_, v___x_703_);
v___x_705_ = lean_string_append(v___x_700_, v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_707_ = lean_string_append(v___x_705_, v___x_706_);
if (lean_obj_tag(v_suffix_x3f_692_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_msg_711_; lean_object* v___x_712_; 
v_val_708_ = lean_ctor_get(v_suffix_x3f_692_, 0);
v___x_709_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_710_ = lean_string_append(v_msg_707_, v___x_709_);
v_msg_711_ = lean_string_append(v___x_710_, v_val_708_);
v___x_712_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_711_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_707_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_713_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v_ty_690_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_716_, lean_object* v_p_717_, lean_object* v_suffix_x3f_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_IR_Checker_checkType(v_ty_716_, v_p_717_, v_suffix_x3f_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_suffix_x3f_718_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_IR_IRType_isObj(v_ty_726_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_msg_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_msg_744_; lean_object* v___x_745_; 
v___x_733_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_734_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_735_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_726_);
v___x_736_ = l_Std_Format_defWidth;
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = l_Std_Format_pretty(v___x_735_, v___x_736_, v___x_737_, v___x_737_);
v___x_739_ = lean_string_append(v___x_734_, v___x_738_);
lean_dec_ref(v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_741_ = lean_string_append(v___x_739_, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_743_ = lean_string_append(v_msg_741_, v___x_742_);
v_msg_744_ = lean_string_append(v___x_743_, v___x_733_);
v___x_745_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_744_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_745_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_ty_726_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_IR_Checker_checkObjType(v_ty_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = l_Lean_IR_IRType_isScalar(v_ty_756_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_msg_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_msg_774_; lean_object* v___x_775_; 
v___x_763_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_764_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_765_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_756_);
v___x_766_ = l_Std_Format_defWidth;
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = l_Std_Format_pretty(v___x_765_, v___x_766_, v___x_767_, v___x_767_);
v___x_769_ = lean_string_append(v___x_764_, v___x_768_);
lean_dec_ref(v___x_768_);
v___x_770_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_771_ = lean_string_append(v___x_769_, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_773_ = lean_string_append(v_msg_771_, v___x_772_);
v_msg_774_ = lean_string_append(v___x_773_, v___x_763_);
v___x_775_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_774_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec(v_ty_756_);
v___x_776_ = lean_box(0);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_IR_Checker_checkScalarType(v_ty_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_localCtx_791_; lean_object* v___x_792_; 
v_localCtx_791_ = lean_ctor_get(v_a_786_, 0);
v___x_792_ = l_Lean_IR_LocalContext_getType(v_localCtx_791_, v_x_785_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_793_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_794_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_795_ = l_Nat_reprFast(v_x_785_);
v___x_796_ = lean_string_append(v___x_794_, v___x_795_);
lean_dec_ref(v___x_795_);
v___x_797_ = lean_string_append(v___x_793_, v___x_796_);
lean_dec_ref(v___x_796_);
v___x_798_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_799_ = lean_string_append(v___x_797_, v___x_798_);
v___x_800_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_799_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_x_785_);
v_val_801_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_792_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_val_801_);
lean_dec(v___x_792_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 0);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_val_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_IR_Checker_getType(v_x_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_816_, lean_object* v_p_817_, lean_object* v_suffix_x3f_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_IR_Checker_getType(v_x_816_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_849_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_849_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_849_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_849_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
lean_inc(v_a_825_);
v___x_829_ = lean_apply_1(v_p_817_, v_a_825_);
v___x_830_ = lean_unbox(v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v_msg_838_; 
lean_del_object(v___x_827_);
v___x_831_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_832_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_825_);
v___x_833_ = l_Std_Format_defWidth;
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = l_Std_Format_pretty(v___x_832_, v___x_833_, v___x_834_, v___x_834_);
v___x_836_ = lean_string_append(v___x_831_, v___x_835_);
lean_dec_ref(v___x_835_);
v___x_837_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_838_ = lean_string_append(v___x_836_, v___x_837_);
if (lean_obj_tag(v_suffix_x3f_818_) == 1)
{
lean_object* v_val_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_msg_842_; lean_object* v___x_843_; 
v_val_839_ = lean_ctor_get(v_suffix_x3f_818_, 0);
v___x_840_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_841_ = lean_string_append(v_msg_838_, v___x_840_);
v_msg_842_ = lean_string_append(v___x_841_, v_val_839_);
v___x_843_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_842_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_838_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
return v___x_844_;
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_847_; 
lean_dec(v_a_825_);
v___x_845_ = lean_box(0);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_845_);
v___x_847_ = v___x_827_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v_p_817_);
v_a_850_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_824_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_824_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_858_, lean_object* v_p_859_, lean_object* v_suffix_x3f_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_IR_Checker_checkVarType(v_x_858_, v_p_859_, v_suffix_x3f_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_suffix_x3f_860_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_IR_Checker_getType(v_x_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_896_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_896_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_896_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_896_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_IR_IRType_isObj(v_a_874_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_msg_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_msg_890_; lean_object* v___x_891_; 
lean_del_object(v___x_876_);
v___x_879_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_880_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_881_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_874_);
v___x_882_ = l_Std_Format_defWidth;
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = l_Std_Format_pretty(v___x_881_, v___x_882_, v___x_883_, v___x_883_);
v___x_885_ = lean_string_append(v___x_880_, v___x_884_);
lean_dec_ref(v___x_884_);
v___x_886_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_887_ = lean_string_append(v___x_885_, v___x_886_);
v___x_888_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_889_ = lean_string_append(v_msg_887_, v___x_888_);
v_msg_890_ = lean_string_append(v___x_889_, v___x_879_);
v___x_891_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_890_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_894_; 
lean_dec(v_a_874_);
v___x_892_ = lean_box(0);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_892_);
v___x_894_ = v___x_876_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_873_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_873_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_IR_Checker_checkObjVar(v_x_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_IR_Checker_getType(v_x_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_941_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_941_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_941_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_941_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
uint8_t v___x_923_; 
v___x_923_ = l_Lean_IR_IRType_isScalar(v_a_919_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_msg_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_msg_935_; lean_object* v___x_936_; 
lean_del_object(v___x_921_);
v___x_924_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_925_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_926_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_919_);
v___x_927_ = l_Std_Format_defWidth;
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l_Std_Format_pretty(v___x_926_, v___x_927_, v___x_928_, v___x_928_);
v___x_930_ = lean_string_append(v___x_925_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_934_ = lean_string_append(v_msg_932_, v___x_933_);
v_msg_935_ = lean_string_append(v___x_934_, v___x_924_);
v___x_936_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_935_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_939_; 
lean_dec(v_a_919_);
v___x_937_ = lean_box(0);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_937_);
v___x_939_ = v___x_921_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_918_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_918_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_IR_Checker_checkScalarVar(v_x_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_961_, lean_object* v_ys_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___x_968_; 
lean_inc(v_c_961_);
v___x_968_ = l_Lean_IR_Checker_getDecl(v_c_961_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = lean_array_get_size(v_ys_962_);
v___x_971_ = l_Lean_IR_Decl_params(v_a_969_);
lean_dec(v_a_969_);
v___x_972_ = lean_array_get_size(v___x_971_);
lean_dec_ref(v___x_971_);
v___x_973_ = lean_nat_dec_eq(v___x_970_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_974_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_975_ = 1;
v___x_976_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_961_, v___x_975_);
v___x_977_ = lean_string_append(v___x_974_, v___x_976_);
lean_dec_ref(v___x_976_);
v___x_978_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
v___x_980_ = l_Nat_reprFast(v___x_970_);
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
v___x_982_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = l_Nat_reprFast(v___x_972_);
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
lean_dec_ref(v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
v___x_988_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_987_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; 
lean_dec(v_c_961_);
v___x_989_ = l_Lean_IR_Checker_checkArgs(v_ys_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
return v___x_989_;
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_c_961_);
v_a_990_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_968_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_968_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_998_, lean_object* v_ys_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_IR_Checker_checkFullApp(v_c_998_, v_ys_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec_ref(v_ys_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1009_, lean_object* v_ys_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; 
lean_inc(v_c_1009_);
v___x_1016_ = l_Lean_IR_Checker_getDecl(v_c_1009_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = lean_array_get_size(v_ys_1010_);
v___x_1019_ = l_Lean_IR_Decl_params(v_a_1017_);
lean_dec(v_a_1017_);
v___x_1020_ = lean_array_get_size(v___x_1019_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = lean_nat_dec_lt(v___x_1018_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1022_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1023_ = 1;
v___x_1024_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1009_, v___x_1023_);
v___x_1025_ = lean_string_append(v___x_1022_, v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1026_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1027_ = lean_string_append(v___x_1025_, v___x_1026_);
v___x_1028_ = l_Nat_reprFast(v___x_1018_);
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
v___x_1032_ = l_Nat_reprFast(v___x_1020_);
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1033_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; 
lean_dec(v_c_1009_);
v___x_1035_ = l_Lean_IR_Checker_checkArgs(v_ys_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
return v___x_1035_;
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v_c_1009_);
v_a_1036_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1016_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1016_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1044_, lean_object* v_ys_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_IR_Checker_checkPartialApp(v_c_1044_, v_ys_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec_ref(v_ys_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1059_, lean_object* v_e_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
switch(lean_obj_tag(v_e_1060_))
{
case 0:
{
lean_object* v_i_1066_; lean_object* v_ys_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v_name_1078_; lean_object* v_cidx_1079_; lean_object* v_size_1080_; lean_object* v_usize_1081_; lean_object* v_ssize_1082_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_i_1066_ = lean_ctor_get(v_e_1060_, 0);
lean_inc_ref(v_i_1066_);
v_ys_1067_ = lean_ctor_get(v_e_1060_, 1);
lean_inc_ref(v_ys_1067_);
lean_dec_ref_known(v_e_1060_, 2);
v_name_1078_ = lean_ctor_get(v_i_1066_, 0);
v_cidx_1079_ = lean_ctor_get(v_i_1066_, 1);
v_size_1080_ = lean_ctor_get(v_i_1066_, 2);
v_usize_1081_ = lean_ctor_get(v_i_1066_, 3);
v_ssize_1082_ = lean_ctor_get(v_i_1066_, 4);
v___x_1114_ = l_Lean_maxCtorTag;
v___x_1115_ = lean_nat_dec_lt(v___x_1114_, v_cidx_1079_);
if (v___x_1115_ == 0)
{
v___y_1101_ = v_a_1061_;
v___y_1102_ = v_a_1062_;
v___y_1103_ = v_a_1063_;
v___y_1104_ = v_a_1064_;
goto v___jp_1100_;
}
else
{
uint8_t v___x_1116_; 
v___x_1116_ = l_Lean_IR_CtorInfo_isRef(v_i_1066_);
if (v___x_1116_ == 0)
{
v___y_1101_ = v_a_1061_;
v___y_1102_ = v_a_1062_;
v___y_1103_ = v_a_1063_;
v___y_1104_ = v_a_1064_;
goto v___jp_1100_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_inc(v_name_1078_);
lean_dec_ref(v_ys_1067_);
lean_dec_ref(v_i_1066_);
lean_dec(v_ty_1059_);
v___x_1117_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1118_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1078_, v___x_1116_);
v___x_1119_ = lean_string_append(v___x_1117_, v___x_1118_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1121_ = lean_string_append(v___x_1119_, v___x_1120_);
v___x_1122_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1121_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1122_;
}
}
v___jp_1068_:
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Lean_IR_CtorInfo_isRef(v_i_1066_);
lean_dec_ref(v_i_1066_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec_ref(v_ys_1067_);
lean_dec(v_ty_1059_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v___x_1077_; 
lean_dec_ref_known(v___x_1076_, 1);
v___x_1077_ = l_Lean_IR_Checker_checkArgs(v_ys_1067_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec_ref(v_ys_1067_);
return v___x_1077_;
}
else
{
lean_dec_ref(v_ys_1067_);
return v___x_1076_;
}
}
}
v___jp_1083_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1088_ = l_Lean_usizeSize;
v___x_1089_ = lean_nat_mul(v_usize_1081_, v___x_1088_);
v___x_1090_ = lean_nat_add(v_ssize_1082_, v___x_1089_);
lean_dec(v___x_1089_);
v___x_1091_ = l_Lean_maxCtorScalarsSize;
v___x_1092_ = lean_nat_dec_lt(v___x_1090_, v___x_1091_);
lean_dec(v___x_1090_);
if (v___x_1092_ == 0)
{
uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_inc(v_name_1078_);
lean_dec_ref(v_ys_1067_);
lean_dec_ref(v_i_1066_);
lean_dec(v_ty_1059_);
v___x_1093_ = 1;
v___x_1094_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1095_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1078_, v___x_1093_);
v___x_1096_ = lean_string_append(v___x_1094_, v___x_1095_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1098_ = lean_string_append(v___x_1096_, v___x_1097_);
v___x_1099_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1098_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
return v___x_1099_;
}
else
{
v___y_1069_ = v___y_1084_;
v___y_1070_ = v___y_1085_;
v___y_1071_ = v___y_1086_;
v___y_1072_ = v___y_1087_;
goto v___jp_1068_;
}
}
v___jp_1100_:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = l_Lean_maxCtorFields;
v___x_1106_ = lean_nat_dec_lt(v_size_1080_, v___x_1105_);
if (v___x_1106_ == 0)
{
uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_inc(v_name_1078_);
lean_dec_ref(v_ys_1067_);
lean_dec_ref(v_i_1066_);
lean_dec(v_ty_1059_);
v___x_1107_ = 1;
v___x_1108_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1109_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1078_, v___x_1107_);
v___x_1110_ = lean_string_append(v___x_1108_, v___x_1109_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
v___x_1113_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1112_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1113_;
}
else
{
v___y_1084_ = v___y_1101_;
v___y_1085_ = v___y_1102_;
v___y_1086_ = v___y_1103_;
v___y_1087_ = v___y_1104_;
goto v___jp_1083_;
}
}
}
case 1:
{
lean_object* v_x_1123_; lean_object* v___x_1124_; 
v_x_1123_ = lean_ctor_get(v_e_1060_, 1);
lean_inc(v_x_1123_);
lean_dec_ref_known(v_e_1060_, 2);
v___x_1124_ = l_Lean_IR_Checker_checkObjVar(v_x_1123_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref_known(v___x_1124_, 1);
v___x_1125_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1125_;
}
else
{
lean_dec(v_ty_1059_);
return v___x_1124_;
}
}
case 2:
{
lean_object* v_x_1126_; lean_object* v_ys_1127_; lean_object* v___x_1128_; 
v_x_1126_ = lean_ctor_get(v_e_1060_, 0);
lean_inc(v_x_1126_);
v_ys_1127_ = lean_ctor_get(v_e_1060_, 2);
lean_inc_ref(v_ys_1127_);
lean_dec_ref_known(v_e_1060_, 3);
v___x_1128_ = l_Lean_IR_Checker_checkObjVar(v_x_1126_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref_known(v___x_1128_, 1);
v___x_1129_ = l_Lean_IR_Checker_checkArgs(v_ys_1127_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_ys_1127_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref_known(v___x_1129_, 1);
v___x_1130_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1130_;
}
else
{
lean_dec(v_ty_1059_);
return v___x_1129_;
}
}
else
{
lean_dec_ref(v_ys_1127_);
lean_dec(v_ty_1059_);
return v___x_1128_;
}
}
case 3:
{
lean_object* v_i_1131_; lean_object* v_x_1132_; lean_object* v___x_1133_; 
v_i_1131_ = lean_ctor_get(v_e_1060_, 0);
lean_inc(v_i_1131_);
v_x_1132_ = lean_ctor_get(v_e_1060_, 1);
lean_inc(v_x_1132_);
lean_dec_ref_known(v_e_1060_, 2);
v___x_1133_ = l_Lean_IR_Checker_getType(v_x_1132_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1179_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1179_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1179_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
switch(lean_obj_tag(v_a_1134_))
{
case 7:
{
lean_object* v___x_1138_; 
lean_del_object(v___x_1136_);
lean_dec(v_i_1131_);
v___x_1138_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1138_;
}
case 8:
{
lean_object* v___x_1139_; 
lean_del_object(v___x_1136_);
lean_dec(v_i_1131_);
v___x_1139_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1139_;
}
case 10:
{
lean_object* v_types_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v_types_1140_ = lean_ctor_get(v_a_1134_, 1);
lean_inc_ref(v_types_1140_);
lean_dec_ref_known(v_a_1134_, 2);
v___x_1141_ = lean_array_get_size(v_types_1140_);
v___x_1142_ = lean_nat_dec_lt(v_i_1131_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec_ref(v_types_1140_);
lean_del_object(v___x_1136_);
lean_dec(v_i_1131_);
lean_dec(v_ty_1059_);
v___x_1143_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1144_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1143_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_array_fget(v_types_1140_, v_i_1131_);
lean_dec(v_i_1131_);
lean_dec_ref(v_types_1140_);
v___x_1146_ = l_Lean_IR_instBEqIRType_beq(v___x_1145_, v_ty_1059_);
lean_dec(v_ty_1059_);
lean_dec(v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_del_object(v___x_1136_);
v___x_1147_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1148_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1147_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(0);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1149_);
v___x_1151_ = v___x_1136_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
case 11:
{
lean_object* v_types_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v_types_1153_ = lean_ctor_get(v_a_1134_, 1);
lean_inc_ref(v_types_1153_);
lean_dec_ref_known(v_a_1134_, 2);
v___x_1154_ = lean_array_get_size(v_types_1153_);
v___x_1155_ = lean_nat_dec_lt(v_i_1131_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v_types_1153_);
lean_del_object(v___x_1136_);
lean_dec(v_i_1131_);
lean_dec(v_ty_1059_);
v___x_1156_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1157_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1156_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_array_fget(v_types_1153_, v_i_1131_);
lean_dec(v_i_1131_);
lean_dec_ref(v_types_1153_);
v___x_1159_ = l_Lean_IR_instBEqIRType_beq(v___x_1158_, v_ty_1059_);
lean_dec(v_ty_1059_);
lean_dec(v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_del_object(v___x_1136_);
v___x_1160_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1161_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1160_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_box(0);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1162_);
v___x_1164_ = v___x_1136_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
case 12:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_dec(v_i_1131_);
lean_dec(v_ty_1059_);
v___x_1166_ = lean_box(0);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1166_);
v___x_1168_ = v___x_1136_;
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
default: 
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_del_object(v___x_1136_);
lean_dec(v_i_1131_);
lean_dec(v_ty_1059_);
v___x_1170_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1171_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1134_);
v___x_1172_ = l_Std_Format_defWidth;
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l_Std_Format_pretty(v___x_1171_, v___x_1172_, v___x_1173_, v___x_1173_);
v___x_1175_ = lean_string_append(v___x_1170_, v___x_1174_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
v___x_1178_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1177_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_i_1131_);
lean_dec(v_ty_1059_);
v_a_1180_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1133_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1133_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
case 4:
{
lean_object* v_x_1188_; lean_object* v___x_1189_; 
v_x_1188_ = lean_ctor_get(v_e_1060_, 1);
lean_inc(v_x_1188_);
lean_dec_ref_known(v_e_1060_, 2);
v___x_1189_ = l_Lean_IR_Checker_checkObjVar(v_x_1188_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1208_; 
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1189_, 0);
lean_dec(v_unused_1209_);
v___x_1191_ = v___x_1189_;
v_isShared_1192_ = v_isSharedCheck_1208_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v___x_1189_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1208_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = lean_box(5);
v___x_1194_ = l_Lean_IR_instBEqIRType_beq(v_ty_1059_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_msg_1202_; lean_object* v___x_1203_; 
lean_del_object(v___x_1191_);
v___x_1195_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1196_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1059_);
v___x_1197_ = l_Std_Format_defWidth;
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = l_Std_Format_pretty(v___x_1196_, v___x_1197_, v___x_1198_, v___x_1198_);
v___x_1200_ = lean_string_append(v___x_1195_, v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1202_ = lean_string_append(v___x_1200_, v___x_1201_);
v___x_1203_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1202_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_dec(v_ty_1059_);
v___x_1204_ = lean_box(0);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1204_);
v___x_1206_ = v___x_1191_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_dec(v_ty_1059_);
return v___x_1189_;
}
}
case 5:
{
lean_object* v_x_1210_; lean_object* v___x_1211_; 
v_x_1210_ = lean_ctor_get(v_e_1060_, 2);
lean_inc(v_x_1210_);
lean_dec_ref_known(v_e_1060_, 3);
v___x_1211_ = l_Lean_IR_Checker_checkObjVar(v_x_1210_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1212_; 
lean_dec_ref_known(v___x_1211_, 1);
v___x_1212_ = l_Lean_IR_Checker_checkScalarType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1212_;
}
else
{
lean_dec(v_ty_1059_);
return v___x_1211_;
}
}
case 6:
{
lean_object* v_c_1213_; lean_object* v_ys_1214_; lean_object* v___x_1215_; 
lean_dec(v_ty_1059_);
v_c_1213_ = lean_ctor_get(v_e_1060_, 0);
lean_inc(v_c_1213_);
v_ys_1214_ = lean_ctor_get(v_e_1060_, 1);
lean_inc_ref(v_ys_1214_);
lean_dec_ref_known(v_e_1060_, 2);
v___x_1215_ = l_Lean_IR_Checker_checkFullApp(v_c_1213_, v_ys_1214_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_ys_1214_);
return v___x_1215_;
}
case 7:
{
lean_object* v_c_1216_; lean_object* v_ys_1217_; lean_object* v___x_1218_; 
v_c_1216_ = lean_ctor_get(v_e_1060_, 0);
lean_inc(v_c_1216_);
v_ys_1217_ = lean_ctor_get(v_e_1060_, 1);
lean_inc_ref(v_ys_1217_);
lean_dec_ref_known(v_e_1060_, 2);
v___x_1218_ = l_Lean_IR_Checker_checkPartialApp(v_c_1216_, v_ys_1217_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_ys_1217_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1219_; 
lean_dec_ref_known(v___x_1218_, 1);
v___x_1219_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1219_;
}
else
{
lean_dec(v_ty_1059_);
return v___x_1218_;
}
}
case 8:
{
lean_object* v_x_1220_; lean_object* v_ys_1221_; lean_object* v___x_1222_; 
v_x_1220_ = lean_ctor_get(v_e_1060_, 0);
lean_inc(v_x_1220_);
v_ys_1221_ = lean_ctor_get(v_e_1060_, 1);
lean_inc_ref(v_ys_1221_);
lean_dec_ref_known(v_e_1060_, 2);
v___x_1222_ = l_Lean_IR_Checker_checkObjVar(v_x_1220_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1223_; 
lean_dec_ref_known(v___x_1222_, 1);
v___x_1223_ = l_Lean_IR_Checker_checkArgs(v_ys_1221_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_ys_1221_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref_known(v___x_1223_, 1);
v___x_1224_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1224_;
}
else
{
lean_dec(v_ty_1059_);
return v___x_1223_;
}
}
else
{
lean_dec_ref(v_ys_1221_);
lean_dec(v_ty_1059_);
return v___x_1222_;
}
}
case 9:
{
lean_object* v_ty_1225_; lean_object* v_x_1226_; lean_object* v___x_1227_; 
v_ty_1225_ = lean_ctor_get(v_e_1060_, 0);
lean_inc(v_ty_1225_);
v_x_1226_ = lean_ctor_get(v_e_1060_, 1);
lean_inc(v_x_1226_);
lean_dec_ref_known(v_e_1060_, 2);
v___x_1227_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref_known(v___x_1227_, 1);
lean_inc(v_x_1226_);
v___x_1228_ = l_Lean_IR_Checker_checkScalarVar(v_x_1226_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref_known(v___x_1228_, 1);
v___x_1229_ = l_Lean_IR_Checker_getType(v_x_1226_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1248_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1248_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1248_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
uint8_t v___x_1234_; 
v___x_1234_ = l_Lean_IR_instBEqIRType_beq(v_a_1230_, v_ty_1225_);
lean_dec(v_ty_1225_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_msg_1242_; lean_object* v___x_1243_; 
lean_del_object(v___x_1232_);
v___x_1235_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1236_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1230_);
v___x_1237_ = l_Std_Format_defWidth;
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = l_Std_Format_pretty(v___x_1236_, v___x_1237_, v___x_1238_, v___x_1238_);
v___x_1240_ = lean_string_append(v___x_1235_, v___x_1239_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1242_ = lean_string_append(v___x_1240_, v___x_1241_);
v___x_1243_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1242_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
lean_dec(v_a_1230_);
v___x_1244_ = lean_box(0);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1244_);
v___x_1246_ = v___x_1232_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_ty_1225_);
v_a_1249_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1229_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1229_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_dec(v_x_1226_);
lean_dec(v_ty_1225_);
return v___x_1228_;
}
}
else
{
lean_dec(v_x_1226_);
lean_dec(v_ty_1225_);
return v___x_1227_;
}
}
case 10:
{
lean_object* v_x_1257_; lean_object* v___x_1258_; 
v_x_1257_ = lean_ctor_get(v_e_1060_, 0);
lean_inc(v_x_1257_);
lean_dec_ref_known(v_e_1060_, 1);
v___x_1258_ = l_Lean_IR_Checker_checkScalarType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; 
lean_dec_ref_known(v___x_1258_, 1);
v___x_1259_ = l_Lean_IR_Checker_checkObjVar(v_x_1257_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1259_;
}
else
{
lean_dec(v_x_1257_);
return v___x_1258_;
}
}
case 11:
{
lean_object* v_v_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1269_; 
v_v_1260_ = lean_ctor_get(v_e_1060_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_e_1060_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1262_ = v_e_1060_;
v_isShared_1263_ = v_isSharedCheck_1269_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_v_1260_);
lean_dec(v_e_1060_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1269_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
if (lean_obj_tag(v_v_1260_) == 1)
{
lean_object* v___x_1264_; 
lean_dec_ref_known(v_v_1260_, 1);
lean_del_object(v___x_1262_);
v___x_1264_ = l_Lean_IR_Checker_checkObjType(v_ty_1059_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_dec_ref(v_v_1260_);
lean_dec(v_ty_1059_);
v___x_1265_ = lean_box(0);
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1265_);
v___x_1267_ = v___x_1262_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
default: 
{
lean_object* v_x_1270_; lean_object* v___x_1271_; 
v_x_1270_ = lean_ctor_get(v_e_1060_, 0);
lean_inc(v_x_1270_);
lean_dec_ref_known(v_e_1060_, 1);
v___x_1271_ = l_Lean_IR_Checker_checkObjVar(v_x_1270_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1290_; 
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v___x_1271_, 0);
lean_dec(v_unused_1291_);
v___x_1273_ = v___x_1271_;
v_isShared_1274_ = v_isSharedCheck_1290_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v___x_1271_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1290_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_box(1);
v___x_1276_ = l_Lean_IR_instBEqIRType_beq(v_ty_1059_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_msg_1284_; lean_object* v___x_1285_; 
lean_del_object(v___x_1273_);
v___x_1277_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1278_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1059_);
v___x_1279_ = l_Std_Format_defWidth;
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = l_Std_Format_pretty(v___x_1278_, v___x_1279_, v___x_1280_, v___x_1280_);
v___x_1282_ = lean_string_append(v___x_1277_, v___x_1281_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
v___x_1285_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1284_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1285_;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_dec(v_ty_1059_);
v___x_1286_ = lean_box(0);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1286_);
v___x_1288_ = v___x_1273_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_dec(v_ty_1059_);
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1292_, lean_object* v_e_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_IR_Checker_checkExpr(v_ty_1292_, v_e_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1300_, lean_object* v_p_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_x_1307_; lean_object* v___x_1308_; 
v_x_1307_ = lean_ctor_get(v_p_1301_, 0);
lean_inc(v_x_1307_);
v___x_1308_ = l_Lean_IR_Checker_markIndex(v_x_1307_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1308_, 0);
lean_dec(v_unused_1317_);
v___x_1310_ = v___x_1308_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_dec(v___x_1308_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = l_Lean_IR_LocalContext_addParam(v_ctx_1300_, v_p_1301_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v_p_1301_);
lean_dec(v_ctx_1300_);
v_a_1318_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1308_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1308_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1326_, lean_object* v_p_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1326_, v_p_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_instMonadEIO(lean_box(0));
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1336_ = l_StateRefT_x27_instMonad___redArg(v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1340_, lean_object* v_k_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v_toApplicative_1348_; lean_object* v_toFunctor_1349_; lean_object* v_toSeq_1350_; lean_object* v_toSeqLeft_1351_; lean_object* v_toSeqRight_1352_; lean_object* v___f_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___x_1357_; lean_object* v___f_1358_; lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_localCtx_1365_; lean_object* v_currentDecl_1366_; lean_object* v_decls_1367_; lean_object* v_a_1369_; lean_object* v___y_1373_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1347_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1348_ = lean_ctor_get(v___x_1347_, 0);
v_toFunctor_1349_ = lean_ctor_get(v_toApplicative_1348_, 0);
v_toSeq_1350_ = lean_ctor_get(v_toApplicative_1348_, 2);
v_toSeqLeft_1351_ = lean_ctor_get(v_toApplicative_1348_, 3);
v_toSeqRight_1352_ = lean_ctor_get(v_toApplicative_1348_, 4);
v___f_1353_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1354_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1349_, 2);
v___f_1355_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1355_, 0, v_toFunctor_1349_);
v___f_1356_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1356_, 0, v_toFunctor_1349_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___f_1355_);
lean_ctor_set(v___x_1357_, 1, v___f_1356_);
lean_inc(v_toSeqRight_1352_);
v___f_1358_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1358_, 0, v_toSeqRight_1352_);
lean_inc(v_toSeqLeft_1351_);
v___f_1359_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1359_, 0, v_toSeqLeft_1351_);
lean_inc(v_toSeq_1350_);
v___f_1360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1360_, 0, v_toSeq_1350_);
v___x_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1357_);
lean_ctor_set(v___x_1361_, 1, v___f_1353_);
lean_ctor_set(v___x_1361_, 2, v___f_1360_);
lean_ctor_set(v___x_1361_, 3, v___f_1359_);
lean_ctor_set(v___x_1361_, 4, v___f_1358_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v___f_1354_);
v___x_1363_ = l_StateRefT_x27_instMonad___redArg(v___x_1362_);
v___x_1364_ = l_ReaderT_instMonad___redArg(v___x_1363_);
v_localCtx_1365_ = lean_ctor_get(v_a_1342_, 0);
v_currentDecl_1366_ = lean_ctor_get(v_a_1342_, 1);
v_decls_1367_ = lean_ctor_get(v_a_1342_, 2);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_array_get_size(v_ps_1340_);
v___x_1385_ = lean_nat_dec_lt(v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v___x_1364_);
lean_dec_ref(v_ps_1340_);
lean_inc(v_localCtx_1365_);
v_a_1369_ = v_localCtx_1365_;
goto v___jp_1368_;
}
else
{
lean_object* v___f_1386_; uint8_t v___x_1387_; 
v___f_1386_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1387_ = lean_nat_dec_le(v___x_1384_, v___x_1384_);
if (v___x_1387_ == 0)
{
if (v___x_1385_ == 0)
{
lean_dec_ref(v___x_1364_);
lean_dec_ref(v_ps_1340_);
lean_inc(v_localCtx_1365_);
v_a_1369_ = v_localCtx_1365_;
goto v___jp_1368_;
}
else
{
size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1038__overap_1390_; lean_object* v___x_1391_; 
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = lean_usize_of_nat(v___x_1384_);
lean_inc(v_localCtx_1365_);
v___x_1038__overap_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1364_, v___f_1386_, v_ps_1340_, v___x_1388_, v___x_1389_, v_localCtx_1365_);
lean_inc(v_a_1345_);
lean_inc_ref(v_a_1344_);
lean_inc(v_a_1343_);
lean_inc_ref(v_a_1342_);
v___x_1391_ = lean_apply_5(v___x_1038__overap_1390_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, lean_box(0));
v___y_1373_ = v___x_1391_;
goto v___jp_1372_;
}
}
else
{
size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1042__overap_1394_; lean_object* v___x_1395_; 
v___x_1392_ = ((size_t)0ULL);
v___x_1393_ = lean_usize_of_nat(v___x_1384_);
lean_inc(v_localCtx_1365_);
v___x_1042__overap_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1364_, v___f_1386_, v_ps_1340_, v___x_1392_, v___x_1393_, v_localCtx_1365_);
lean_inc(v_a_1345_);
lean_inc_ref(v_a_1344_);
lean_inc(v_a_1343_);
lean_inc_ref(v_a_1342_);
v___x_1395_ = lean_apply_5(v___x_1042__overap_1394_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, lean_box(0));
v___y_1373_ = v___x_1395_;
goto v___jp_1372_;
}
}
v___jp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_inc_ref(v_decls_1367_);
lean_inc_ref(v_currentDecl_1366_);
v___x_1370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1369_);
lean_ctor_set(v___x_1370_, 1, v_currentDecl_1366_);
lean_ctor_set(v___x_1370_, 2, v_decls_1367_);
lean_inc(v_a_1345_);
lean_inc_ref(v_a_1344_);
lean_inc(v_a_1343_);
v___x_1371_ = lean_apply_5(v_k_1341_, v___x_1370_, v_a_1343_, v_a_1344_, v_a_1345_, lean_box(0));
return v___x_1371_;
}
v___jp_1372_:
{
if (lean_obj_tag(v___y_1373_) == 0)
{
lean_object* v_a_1374_; 
v_a_1374_ = lean_ctor_get(v___y_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___y_1373_, 1);
v_a_1369_ = v_a_1374_;
goto v___jp_1368_;
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec_ref(v_k_1341_);
v_a_1375_ = lean_ctor_get(v___y_1373_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___y_1373_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___y_1373_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___y_1373_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1396_, lean_object* v_k_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_IR_Checker_withParams(v_ps_1396_, v_k_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1404_, size_t v_i_1405_, size_t v_stop_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_usize_dec_eq(v_i_1405_, v_stop_1406_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v_x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = lean_array_uget_borrowed(v_as_1404_, v_i_1405_);
v_x_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_x_1415_);
v___x_1416_ = l_Lean_IR_Checker_markIndex(v_x_1415_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; 
lean_dec_ref_known(v___x_1416_, 1);
lean_inc(v___x_1414_);
v___x_1417_ = l_Lean_IR_LocalContext_addParam(v_b_1407_, v___x_1414_);
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = lean_usize_add(v_i_1405_, v___x_1418_);
v_i_1405_ = v___x_1419_;
v_b_1407_ = v___x_1417_;
goto _start;
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_b_1407_);
v_a_1421_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1416_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1416_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v_b_1407_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1430_, lean_object* v_i_1431_, lean_object* v_stop_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
size_t v_i_boxed_1439_; size_t v_stop_boxed_1440_; lean_object* v_res_1441_; 
v_i_boxed_1439_ = lean_unbox_usize(v_i_1431_);
lean_dec(v_i_1431_);
v_stop_boxed_1440_ = lean_unbox_usize(v_stop_1432_);
lean_dec(v_stop_1432_);
v_res_1441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1430_, v_i_boxed_1439_, v_stop_boxed_1440_, v_b_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec_ref(v_as_1430_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_x_1449_; lean_object* v_b_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; 
switch(lean_obj_tag(v_fnBody_1442_))
{
case 0:
{
lean_object* v_x_1457_; lean_object* v_ty_1458_; lean_object* v_e_1459_; lean_object* v_b_1460_; lean_object* v___x_1461_; 
v_x_1457_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_x_1457_);
v_ty_1458_ = lean_ctor_get(v_fnBody_1442_, 1);
lean_inc_n(v_ty_1458_, 2);
v_e_1459_ = lean_ctor_get(v_fnBody_1442_, 2);
lean_inc_ref_n(v_e_1459_, 2);
v_b_1460_ = lean_ctor_get(v_fnBody_1442_, 3);
lean_inc(v_b_1460_);
lean_dec_ref_known(v_fnBody_1442_, 4);
v___x_1461_ = l_Lean_IR_Checker_checkExpr(v_ty_1458_, v_e_1459_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1462_; 
lean_dec_ref_known(v___x_1461_, 1);
lean_inc(v_x_1457_);
v___x_1462_ = l_Lean_IR_Checker_markIndex(v_x_1457_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_localCtx_1463_; lean_object* v_currentDecl_1464_; lean_object* v_decls_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref_known(v___x_1462_, 1);
v_localCtx_1463_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_localCtx_1463_);
v_currentDecl_1464_ = lean_ctor_get(v_a_1443_, 1);
lean_inc_ref(v_currentDecl_1464_);
v_decls_1465_ = lean_ctor_get(v_a_1443_, 2);
lean_inc_ref(v_decls_1465_);
lean_dec_ref(v_a_1443_);
v___x_1466_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1463_, v_x_1457_, v_ty_1458_, v_e_1459_);
v___x_1467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_currentDecl_1464_);
lean_ctor_set(v___x_1467_, 2, v_decls_1465_);
v_fnBody_1442_ = v_b_1460_;
v_a_1443_ = v___x_1467_;
goto _start;
}
else
{
lean_dec(v_b_1460_);
lean_dec_ref(v_e_1459_);
lean_dec(v_ty_1458_);
lean_dec(v_x_1457_);
lean_dec_ref(v_a_1443_);
return v___x_1462_;
}
}
else
{
lean_dec(v_b_1460_);
lean_dec_ref(v_e_1459_);
lean_dec(v_ty_1458_);
lean_dec(v_x_1457_);
lean_dec_ref(v_a_1443_);
return v___x_1461_;
}
}
case 1:
{
lean_object* v_j_1469_; lean_object* v_xs_1470_; lean_object* v_v_1471_; lean_object* v_b_1472_; lean_object* v___x_1473_; 
v_j_1469_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc_n(v_j_1469_, 2);
v_xs_1470_ = lean_ctor_get(v_fnBody_1442_, 1);
lean_inc_ref(v_xs_1470_);
v_v_1471_ = lean_ctor_get(v_fnBody_1442_, 2);
lean_inc(v_v_1471_);
v_b_1472_ = lean_ctor_get(v_fnBody_1442_, 3);
lean_inc(v_b_1472_);
lean_dec_ref_known(v_fnBody_1442_, 4);
v___x_1473_ = l_Lean_IR_Checker_markIndex(v_j_1469_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_localCtx_1474_; lean_object* v_currentDecl_1475_; lean_object* v_decls_1476_; lean_object* v_a_1478_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
lean_dec_ref_known(v___x_1473_, 1);
v_localCtx_1474_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_localCtx_1474_);
v_currentDecl_1475_ = lean_ctor_get(v_a_1443_, 1);
lean_inc_ref(v_currentDecl_1475_);
v_decls_1476_ = lean_ctor_get(v_a_1443_, 2);
lean_inc_ref(v_decls_1476_);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_array_get_size(v_xs_1470_);
v___x_1486_ = lean_nat_dec_lt(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_dec_ref(v_a_1443_);
lean_inc(v_localCtx_1474_);
v_a_1478_ = v_localCtx_1474_;
goto v___jp_1477_;
}
else
{
size_t v___x_1487_; size_t v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = lean_usize_of_nat(v___x_1485_);
lean_inc(v_localCtx_1474_);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1470_, v___x_1487_, v___x_1488_, v_localCtx_1474_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec_ref(v_a_1443_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v_a_1478_ = v_a_1490_;
goto v___jp_1477_;
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_decls_1476_);
lean_dec_ref(v_currentDecl_1475_);
lean_dec(v_localCtx_1474_);
lean_dec(v_b_1472_);
lean_dec(v_v_1471_);
lean_dec_ref(v_xs_1470_);
lean_dec(v_j_1469_);
v_a_1491_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1489_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1489_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
v___jp_1477_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_inc_ref(v_decls_1476_);
lean_inc_ref(v_currentDecl_1475_);
v___x_1479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1479_, 0, v_a_1478_);
lean_ctor_set(v___x_1479_, 1, v_currentDecl_1475_);
lean_ctor_set(v___x_1479_, 2, v_decls_1476_);
lean_inc(v_v_1471_);
v___x_1480_ = l_Lean_IR_Checker_checkFnBody(v_v_1471_, v___x_1479_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref_known(v___x_1480_, 1);
v___x_1481_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1474_, v_j_1469_, v_xs_1470_, v_v_1471_);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_currentDecl_1475_);
lean_ctor_set(v___x_1482_, 2, v_decls_1476_);
v_fnBody_1442_ = v_b_1472_;
v_a_1443_ = v___x_1482_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1476_);
lean_dec_ref(v_currentDecl_1475_);
lean_dec(v_localCtx_1474_);
lean_dec(v_b_1472_);
lean_dec(v_v_1471_);
lean_dec_ref(v_xs_1470_);
lean_dec(v_j_1469_);
return v___x_1480_;
}
}
}
else
{
lean_dec(v_b_1472_);
lean_dec(v_v_1471_);
lean_dec_ref(v_xs_1470_);
lean_dec(v_j_1469_);
lean_dec_ref(v_a_1443_);
return v___x_1473_;
}
}
case 2:
{
lean_object* v_x_1499_; lean_object* v_y_1500_; lean_object* v_b_1501_; lean_object* v___x_1502_; 
v_x_1499_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_x_1499_);
v_y_1500_ = lean_ctor_get(v_fnBody_1442_, 2);
lean_inc(v_y_1500_);
v_b_1501_ = lean_ctor_get(v_fnBody_1442_, 3);
lean_inc(v_b_1501_);
lean_dec_ref_known(v_fnBody_1442_, 4);
v___x_1502_ = l_Lean_IR_Checker_checkVar(v_x_1499_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1503_; 
lean_dec_ref_known(v___x_1502_, 1);
v___x_1503_ = l_Lean_IR_Checker_checkArg(v_y_1500_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_dec_ref_known(v___x_1503_, 1);
v_fnBody_1442_ = v_b_1501_;
goto _start;
}
else
{
lean_dec(v_b_1501_);
lean_dec_ref(v_a_1443_);
return v___x_1503_;
}
}
else
{
lean_dec(v_b_1501_);
lean_dec(v_y_1500_);
lean_dec_ref(v_a_1443_);
return v___x_1502_;
}
}
case 3:
{
lean_object* v_x_1505_; lean_object* v_b_1506_; lean_object* v___x_1507_; 
v_x_1505_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_x_1505_);
v_b_1506_ = lean_ctor_get(v_fnBody_1442_, 2);
lean_inc(v_b_1506_);
lean_dec_ref_known(v_fnBody_1442_, 3);
v___x_1507_ = l_Lean_IR_Checker_checkVar(v_x_1505_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_dec_ref_known(v___x_1507_, 1);
v_fnBody_1442_ = v_b_1506_;
goto _start;
}
else
{
lean_dec(v_b_1506_);
lean_dec_ref(v_a_1443_);
return v___x_1507_;
}
}
case 4:
{
lean_object* v_x_1509_; lean_object* v_y_1510_; lean_object* v_b_1511_; lean_object* v___x_1512_; 
v_x_1509_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_x_1509_);
v_y_1510_ = lean_ctor_get(v_fnBody_1442_, 2);
lean_inc(v_y_1510_);
v_b_1511_ = lean_ctor_get(v_fnBody_1442_, 3);
lean_inc(v_b_1511_);
lean_dec_ref_known(v_fnBody_1442_, 4);
v___x_1512_ = l_Lean_IR_Checker_checkVar(v_x_1509_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref_known(v___x_1512_, 1);
v___x_1513_ = l_Lean_IR_Checker_checkVar(v_y_1510_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_dec_ref_known(v___x_1513_, 1);
v_fnBody_1442_ = v_b_1511_;
goto _start;
}
else
{
lean_dec(v_b_1511_);
lean_dec_ref(v_a_1443_);
return v___x_1513_;
}
}
else
{
lean_dec(v_b_1511_);
lean_dec(v_y_1510_);
lean_dec_ref(v_a_1443_);
return v___x_1512_;
}
}
case 5:
{
lean_object* v_x_1515_; lean_object* v_y_1516_; lean_object* v_b_1517_; lean_object* v___x_1518_; 
v_x_1515_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_x_1515_);
v_y_1516_ = lean_ctor_get(v_fnBody_1442_, 3);
lean_inc(v_y_1516_);
v_b_1517_ = lean_ctor_get(v_fnBody_1442_, 5);
lean_inc(v_b_1517_);
lean_dec_ref_known(v_fnBody_1442_, 6);
v___x_1518_ = l_Lean_IR_Checker_checkVar(v_x_1515_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v___x_1519_; 
lean_dec_ref_known(v___x_1518_, 1);
v___x_1519_ = l_Lean_IR_Checker_checkVar(v_y_1516_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_dec_ref_known(v___x_1519_, 1);
v_fnBody_1442_ = v_b_1517_;
goto _start;
}
else
{
lean_dec(v_b_1517_);
lean_dec_ref(v_a_1443_);
return v___x_1519_;
}
}
else
{
lean_dec(v_b_1517_);
lean_dec(v_y_1516_);
lean_dec_ref(v_a_1443_);
return v___x_1518_;
}
}
case 8:
{
lean_object* v_x_1521_; lean_object* v_b_1522_; lean_object* v___x_1523_; 
v_x_1521_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_x_1521_);
v_b_1522_ = lean_ctor_get(v_fnBody_1442_, 1);
lean_inc(v_b_1522_);
lean_dec_ref_known(v_fnBody_1442_, 2);
v___x_1523_ = l_Lean_IR_Checker_checkVar(v_x_1521_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_dec_ref_known(v___x_1523_, 1);
v_fnBody_1442_ = v_b_1522_;
goto _start;
}
else
{
lean_dec(v_b_1522_);
lean_dec_ref(v_a_1443_);
return v___x_1523_;
}
}
case 9:
{
lean_object* v_x_1525_; lean_object* v_cs_1526_; lean_object* v___x_1527_; 
v_x_1525_ = lean_ctor_get(v_fnBody_1442_, 1);
lean_inc(v_x_1525_);
v_cs_1526_ = lean_ctor_get(v_fnBody_1442_, 3);
lean_inc_ref(v_cs_1526_);
lean_dec_ref_known(v_fnBody_1442_, 4);
v___x_1527_ = l_Lean_IR_Checker_checkVar(v_x_1525_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1548_; 
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v___x_1527_, 0);
lean_dec(v_unused_1549_);
v___x_1529_ = v___x_1527_;
v_isShared_1530_ = v_isSharedCheck_1548_;
goto v_resetjp_1528_;
}
else
{
lean_dec(v___x_1527_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1548_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_array_get_size(v_cs_1526_);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_nat_dec_lt(v___x_1531_, v___x_1532_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1536_; 
lean_dec_ref(v_cs_1526_);
lean_dec_ref(v_a_1443_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1533_);
v___x_1536_ = v___x_1529_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1533_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_nat_dec_le(v___x_1532_, v___x_1532_);
if (v___x_1538_ == 0)
{
if (v___x_1534_ == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref(v_cs_1526_);
lean_dec_ref(v_a_1443_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1533_);
v___x_1540_ = v___x_1529_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1533_);
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
size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
lean_del_object(v___x_1529_);
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = lean_usize_of_nat(v___x_1532_);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1526_, v___x_1542_, v___x_1543_, v___x_1533_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v_cs_1526_);
return v___x_1544_;
}
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
lean_del_object(v___x_1529_);
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = lean_usize_of_nat(v___x_1532_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1526_, v___x_1545_, v___x_1546_, v___x_1533_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v_cs_1526_);
return v___x_1547_;
}
}
}
}
else
{
lean_dec_ref(v_cs_1526_);
lean_dec_ref(v_a_1443_);
return v___x_1527_;
}
}
case 10:
{
lean_object* v_x_1550_; lean_object* v___x_1551_; 
v_x_1550_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_x_1550_);
lean_dec_ref_known(v_fnBody_1442_, 1);
v___x_1551_ = l_Lean_IR_Checker_checkArg(v_x_1550_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec_ref(v_a_1443_);
return v___x_1551_;
}
case 11:
{
lean_object* v_j_1552_; lean_object* v_ys_1553_; lean_object* v___x_1554_; 
v_j_1552_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_j_1552_);
v_ys_1553_ = lean_ctor_get(v_fnBody_1442_, 1);
lean_inc_ref(v_ys_1553_);
lean_dec_ref_known(v_fnBody_1442_, 2);
v___x_1554_ = l_Lean_IR_Checker_checkJP(v_j_1552_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref_known(v___x_1554_, 1);
v___x_1555_ = l_Lean_IR_Checker_checkArgs(v_ys_1553_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v_ys_1553_);
return v___x_1555_;
}
else
{
lean_dec_ref(v_ys_1553_);
lean_dec_ref(v_a_1443_);
return v___x_1554_;
}
}
case 12:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref(v_a_1443_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
default: 
{
lean_object* v_x_1558_; lean_object* v_b_1559_; 
v_x_1558_ = lean_ctor_get(v_fnBody_1442_, 0);
lean_inc(v_x_1558_);
v_b_1559_ = lean_ctor_get(v_fnBody_1442_, 2);
lean_inc(v_b_1559_);
lean_dec(v_fnBody_1442_);
v_x_1449_ = v_x_1558_;
v_b_1450_ = v_b_1559_;
v___y_1451_ = v_a_1443_;
v___y_1452_ = v_a_1444_;
v___y_1453_ = v_a_1445_;
v___y_1454_ = v_a_1446_;
goto v___jp_1448_;
}
}
v___jp_1448_:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_IR_Checker_checkVar(v_x_1449_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_dec_ref_known(v___x_1455_, 1);
v_fnBody_1442_ = v_b_1450_;
v_a_1443_ = v___y_1451_;
v_a_1444_ = v___y_1452_;
v_a_1445_ = v___y_1453_;
v_a_1446_ = v___y_1454_;
goto _start;
}
else
{
lean_dec_ref(v___y_1451_);
lean_dec(v_b_1450_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1560_, size_t v_i_1561_, size_t v_stop_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_usize_dec_eq(v_i_1561_, v_stop_1562_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_array_uget_borrowed(v_as_1560_, v_i_1561_);
v___x_1571_ = l_Lean_IR_Alt_body(v___x_1570_);
lean_inc_ref(v___y_1564_);
v___x_1572_ = l_Lean_IR_Checker_checkFnBody(v___x_1571_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; size_t v___x_1574_; size_t v___x_1575_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = ((size_t)1ULL);
v___x_1575_ = lean_usize_add(v_i_1561_, v___x_1574_);
v_i_1561_ = v___x_1575_;
v_b_1563_ = v_a_1573_;
goto _start;
}
else
{
return v___x_1572_;
}
}
else
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_b_1563_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1578_, lean_object* v_i_1579_, lean_object* v_stop_1580_, lean_object* v_b_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
size_t v_i_boxed_1587_; size_t v_stop_boxed_1588_; lean_object* v_res_1589_; 
v_i_boxed_1587_ = lean_unbox_usize(v_i_1579_);
lean_dec(v_i_1579_);
v_stop_boxed_1588_ = lean_unbox_usize(v_stop_1580_);
lean_dec(v_stop_1580_);
v_res_1589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1578_, v_i_boxed_1587_, v_stop_boxed_1588_, v_b_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec_ref(v_as_1578_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
if (lean_obj_tag(v_x_1597_) == 0)
{
lean_object* v_xs_1603_; lean_object* v_body_1604_; lean_object* v_localCtx_1605_; lean_object* v_currentDecl_1606_; lean_object* v_decls_1607_; lean_object* v_a_1609_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_xs_1603_ = lean_ctor_get(v_x_1597_, 1);
lean_inc_ref(v_xs_1603_);
v_body_1604_ = lean_ctor_get(v_x_1597_, 3);
lean_inc(v_body_1604_);
lean_dec_ref_known(v_x_1597_, 5);
v_localCtx_1605_ = lean_ctor_get(v_a_1598_, 0);
v_currentDecl_1606_ = lean_ctor_get(v_a_1598_, 1);
v_decls_1607_ = lean_ctor_get(v_a_1598_, 2);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_array_get_size(v_xs_1603_);
v___x_1614_ = lean_nat_dec_lt(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_dec_ref(v_xs_1603_);
lean_inc(v_localCtx_1605_);
v_a_1609_ = v_localCtx_1605_;
goto v___jp_1608_;
}
else
{
size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = lean_usize_of_nat(v___x_1613_);
lean_inc(v_localCtx_1605_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1603_, v___x_1615_, v___x_1616_, v_localCtx_1605_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec_ref(v_xs_1603_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v_a_1609_ = v_a_1618_;
goto v___jp_1608_;
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_body_1604_);
v_a_1619_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1617_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1617_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
v___jp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_inc_ref(v_decls_1607_);
lean_inc_ref(v_currentDecl_1606_);
v___x_1610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1610_, 0, v_a_1609_);
lean_ctor_set(v___x_1610_, 1, v_currentDecl_1606_);
lean_ctor_set(v___x_1610_, 2, v_decls_1607_);
v___x_1611_ = l_Lean_IR_Checker_checkFnBody(v_body_1604_, v___x_1610_, v_a_1599_, v_a_1600_, v_a_1601_);
return v___x_1611_;
}
}
else
{
lean_object* v_xs_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_xs_1627_ = lean_ctor_get(v_x_1597_, 1);
lean_inc_ref(v_xs_1627_);
lean_dec_ref_known(v_x_1597_, 4);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_array_get_size(v_xs_1627_);
v___x_1631_ = lean_nat_dec_lt(v___x_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v_xs_1627_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1628_);
return v___x_1632_;
}
else
{
lean_object* v_localCtx_1633_; size_t v___x_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
v_localCtx_1633_ = lean_ctor_get(v_a_1598_, 0);
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = lean_usize_of_nat(v___x_1630_);
lean_inc(v_localCtx_1633_);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1627_, v___x_1634_, v___x_1635_, v_localCtx_1633_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec_ref(v_xs_1627_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v___x_1636_, 0);
lean_dec(v_unused_1644_);
v___x_1638_ = v___x_1636_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v___x_1636_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1628_);
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1628_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1636_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1636_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_IR_Checker_checkDecl(v_x_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_1660_, lean_object* v_decl_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1665_ = lean_box(1);
v___x_1666_ = lean_st_mk_ref(v___x_1665_);
lean_inc_ref(v_decl_1661_);
v___x_1667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v_decl_1661_);
lean_ctor_set(v___x_1667_, 2, v_decls_1660_);
v___x_1668_ = l_Lean_IR_Checker_checkDecl(v_decl_1661_, v___x_1667_, v___x_1666_, v_a_1662_, v_a_1663_);
lean_dec_ref_known(v___x_1667_, 3);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_st_ref_get(v___x_1666_);
lean_dec(v___x_1666_);
lean_dec(v___x_1673_);
if (v_isShared_1672_ == 0)
{
v___x_1675_ = v___x_1671_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1669_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_dec(v___x_1666_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* v_decls_1678_, lean_object* v_decl_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_IR_checkDecl(v_decls_1678_, v_decl_1679_, v_a_1680_, v_a_1681_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* v_decls_1684_, lean_object* v_as_1685_, size_t v_i_1686_, size_t v_stop_1687_, lean_object* v_b_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_usize_dec_eq(v_i_1686_, v_stop_1687_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_array_uget_borrowed(v_as_1685_, v_i_1686_);
lean_inc(v___x_1693_);
lean_inc_ref(v_decls_1684_);
v___x_1694_ = l_Lean_IR_checkDecl(v_decls_1684_, v___x_1693_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; size_t v___x_1696_; size_t v___x_1697_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v___x_1696_ = ((size_t)1ULL);
v___x_1697_ = lean_usize_add(v_i_1686_, v___x_1696_);
v_i_1686_ = v___x_1697_;
v_b_1688_ = v_a_1695_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1684_);
return v___x_1694_;
}
}
else
{
lean_object* v___x_1699_; 
lean_dec_ref(v_decls_1684_);
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_b_1688_);
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* v_decls_1700_, lean_object* v_as_1701_, lean_object* v_i_1702_, lean_object* v_stop_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
size_t v_i_boxed_1708_; size_t v_stop_boxed_1709_; lean_object* v_res_1710_; 
v_i_boxed_1708_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_stop_boxed_1709_ = lean_unbox_usize(v_stop_1703_);
lean_dec(v_stop_1703_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1700_, v_as_1701_, v_i_boxed_1708_, v_stop_boxed_1709_, v_b_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec_ref(v_as_1701_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* v_decls_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = lean_array_get_size(v_decls_1711_);
v___x_1717_ = lean_box(0);
v___x_1718_ = lean_nat_dec_lt(v___x_1715_, v___x_1716_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_dec_ref(v_decls_1711_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = lean_nat_dec_le(v___x_1716_, v___x_1716_);
if (v___x_1720_ == 0)
{
if (v___x_1718_ == 0)
{
lean_object* v___x_1721_; 
lean_dec_ref(v_decls_1711_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1717_);
return v___x_1721_;
}
else
{
size_t v___x_1722_; size_t v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = ((size_t)0ULL);
v___x_1723_ = lean_usize_of_nat(v___x_1716_);
lean_inc_ref(v_decls_1711_);
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1711_, v_decls_1711_, v___x_1722_, v___x_1723_, v___x_1717_, v_a_1712_, v_a_1713_);
lean_dec_ref(v_decls_1711_);
return v___x_1724_;
}
}
else
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = lean_usize_of_nat(v___x_1716_);
lean_inc_ref(v_decls_1711_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1711_, v_decls_1711_, v___x_1725_, v___x_1726_, v___x_1717_, v_a_1712_, v_a_1713_);
lean_dec_ref(v_decls_1711_);
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_IR_checkDecls(v_decls_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1732_;
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
