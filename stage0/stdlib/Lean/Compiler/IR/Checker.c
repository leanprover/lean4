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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_IR_Decl_name(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxCtorScalarsSize;
extern lean_object* l_Lean_usizeSize;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_maxCtorNumObjs;
extern lean_object* l_Lean_maxCtorTag;
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqIRType_beq(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_getDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "depends on declaration '"};
static const lean_object* l_Lean_IR_Checker_getDecl___closed__0 = (const lean_object*)&l_Lean_IR_Checker_getDecl___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_getDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "', which has no executable code; consider marking definition as 'noncomputable'"};
static const lean_object* l_Lean_IR_Checker_getDecl___closed__1 = (const lean_object*)&l_Lean_IR_Checker_getDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(lean_object* v_k_122_, lean_object* v_t_123_){
_start:
{
if (lean_obj_tag(v_t_123_) == 0)
{
lean_object* v_k_124_; lean_object* v_l_125_; lean_object* v_r_126_; uint8_t v___x_127_; 
v_k_124_ = lean_ctor_get(v_t_123_, 1);
v_l_125_ = lean_ctor_get(v_t_123_, 3);
v_r_126_ = lean_ctor_get(v_t_123_, 4);
v___x_127_ = lean_nat_dec_lt(v_k_122_, v_k_124_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_eq(v_k_122_, v_k_124_);
if (v___x_128_ == 0)
{
v_t_123_ = v_r_126_;
goto _start;
}
else
{
return v___x_128_;
}
}
else
{
v_t_123_ = v_l_125_;
goto _start;
}
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg___boxed(lean_object* v_k_132_, lean_object* v_t_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_k_132_, v_t_133_);
lean_dec(v_t_133_);
lean_dec(v_k_132_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(lean_object* v_k_136_, lean_object* v_v_137_, lean_object* v_t_138_){
_start:
{
if (lean_obj_tag(v_t_138_) == 0)
{
lean_object* v_size_139_; lean_object* v_k_140_; lean_object* v_v_141_; lean_object* v_l_142_; lean_object* v_r_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_424_; 
v_size_139_ = lean_ctor_get(v_t_138_, 0);
v_k_140_ = lean_ctor_get(v_t_138_, 1);
v_v_141_ = lean_ctor_get(v_t_138_, 2);
v_l_142_ = lean_ctor_get(v_t_138_, 3);
v_r_143_ = lean_ctor_get(v_t_138_, 4);
v_isSharedCheck_424_ = !lean_is_exclusive(v_t_138_);
if (v_isSharedCheck_424_ == 0)
{
v___x_145_ = v_t_138_;
v_isShared_146_ = v_isSharedCheck_424_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_r_143_);
lean_inc(v_l_142_);
lean_inc(v_v_141_);
lean_inc(v_k_140_);
lean_inc(v_size_139_);
lean_dec(v_t_138_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_424_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
uint8_t v___x_147_; 
v___x_147_ = lean_nat_dec_lt(v_k_136_, v_k_140_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_eq(v_k_136_, v_k_140_);
if (v___x_148_ == 0)
{
lean_object* v_impl_149_; lean_object* v___x_150_; 
lean_dec(v_size_139_);
v_impl_149_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_k_136_, v_v_137_, v_r_143_);
v___x_150_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_142_) == 0)
{
lean_object* v_size_151_; lean_object* v_size_152_; lean_object* v_k_153_; lean_object* v_v_154_; lean_object* v_l_155_; lean_object* v_r_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_size_151_ = lean_ctor_get(v_l_142_, 0);
v_size_152_ = lean_ctor_get(v_impl_149_, 0);
v_k_153_ = lean_ctor_get(v_impl_149_, 1);
v_v_154_ = lean_ctor_get(v_impl_149_, 2);
v_l_155_ = lean_ctor_get(v_impl_149_, 3);
lean_inc(v_l_155_);
v_r_156_ = lean_ctor_get(v_impl_149_, 4);
v___x_157_ = lean_unsigned_to_nat(3u);
v___x_158_ = lean_nat_mul(v___x_157_, v_size_151_);
v___x_159_ = lean_nat_dec_lt(v___x_158_, v_size_152_);
lean_dec(v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
lean_dec(v_l_155_);
v___x_160_ = lean_nat_add(v___x_150_, v_size_151_);
v___x_161_ = lean_nat_add(v___x_160_, v_size_152_);
lean_dec(v___x_160_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_impl_149_);
lean_ctor_set(v___x_145_, 0, v___x_161_);
v___x_163_ = v___x_145_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v_l_142_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v_impl_149_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
else
{
lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_228_; 
lean_inc(v_r_156_);
lean_inc(v_v_154_);
lean_inc(v_k_153_);
lean_inc(v_size_152_);
v_isSharedCheck_228_ = !lean_is_exclusive(v_impl_149_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_229_ = lean_ctor_get(v_impl_149_, 4);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_impl_149_, 3);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_impl_149_, 2);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_impl_149_, 1);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_impl_149_, 0);
lean_dec(v_unused_233_);
v___x_166_ = v_impl_149_;
v_isShared_167_ = v_isSharedCheck_228_;
goto v_resetjp_165_;
}
else
{
lean_dec(v_impl_149_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_228_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_size_168_; lean_object* v_k_169_; lean_object* v_v_170_; lean_object* v_l_171_; lean_object* v_r_172_; lean_object* v_size_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_size_168_ = lean_ctor_get(v_l_155_, 0);
v_k_169_ = lean_ctor_get(v_l_155_, 1);
v_v_170_ = lean_ctor_get(v_l_155_, 2);
v_l_171_ = lean_ctor_get(v_l_155_, 3);
v_r_172_ = lean_ctor_get(v_l_155_, 4);
v_size_173_ = lean_ctor_get(v_r_156_, 0);
v___x_174_ = lean_unsigned_to_nat(2u);
v___x_175_ = lean_nat_mul(v___x_174_, v_size_173_);
v___x_176_ = lean_nat_dec_lt(v_size_168_, v___x_175_);
lean_dec(v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_204_; 
lean_inc(v_r_172_);
lean_inc(v_l_171_);
lean_inc(v_v_170_);
lean_inc(v_k_169_);
v_isSharedCheck_204_ = !lean_is_exclusive(v_l_155_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; lean_object* v_unused_209_; 
v_unused_205_ = lean_ctor_get(v_l_155_, 4);
lean_dec(v_unused_205_);
v_unused_206_ = lean_ctor_get(v_l_155_, 3);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_l_155_, 2);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_l_155_, 1);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_l_155_, 0);
lean_dec(v_unused_209_);
v___x_178_ = v_l_155_;
v_isShared_179_ = v_isSharedCheck_204_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_l_155_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_204_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_194_; 
v___x_180_ = lean_nat_add(v___x_150_, v_size_151_);
v___x_181_ = lean_nat_add(v___x_180_, v_size_152_);
lean_dec(v_size_152_);
if (lean_obj_tag(v_l_171_) == 0)
{
lean_object* v_size_202_; 
v_size_202_ = lean_ctor_get(v_l_171_, 0);
lean_inc(v_size_202_);
v___y_194_ = v_size_202_;
goto v___jp_193_;
}
else
{
lean_object* v___x_203_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___y_194_ = v___x_203_;
goto v___jp_193_;
}
v___jp_182_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_nat_add(v___y_183_, v___y_185_);
lean_dec(v___y_185_);
lean_dec(v___y_183_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v_r_156_);
lean_ctor_set(v___x_178_, 3, v_r_172_);
lean_ctor_set(v___x_178_, 2, v_v_154_);
lean_ctor_set(v___x_178_, 1, v_k_153_);
lean_ctor_set(v___x_178_, 0, v___x_186_);
v___x_188_ = v___x_178_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_k_153_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_v_154_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_r_172_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v_r_156_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 4, v___x_188_);
lean_ctor_set(v___x_166_, 3, v___y_184_);
lean_ctor_set(v___x_166_, 2, v_v_170_);
lean_ctor_set(v___x_166_, 1, v_k_169_);
lean_ctor_set(v___x_166_, 0, v___x_181_);
v___x_190_ = v___x_166_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v___y_184_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_nat_add(v___x_180_, v___y_194_);
lean_dec(v___y_194_);
lean_dec(v___x_180_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_l_171_);
lean_ctor_set(v___x_145_, 0, v___x_195_);
v___x_197_ = v___x_145_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_l_142_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_l_171_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = lean_nat_add(v___x_150_, v_size_173_);
if (lean_obj_tag(v_r_172_) == 0)
{
lean_object* v_size_199_; 
v_size_199_ = lean_ctor_get(v_r_172_, 0);
lean_inc(v_size_199_);
v___y_183_ = v___x_198_;
v___y_184_ = v___x_197_;
v___y_185_ = v_size_199_;
goto v___jp_182_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___y_183_ = v___x_198_;
v___y_184_ = v___x_197_;
v___y_185_ = v___x_200_;
goto v___jp_182_;
}
}
}
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
lean_del_object(v___x_145_);
v___x_210_ = lean_nat_add(v___x_150_, v_size_151_);
v___x_211_ = lean_nat_add(v___x_210_, v_size_152_);
lean_dec(v_size_152_);
v___x_212_ = lean_nat_add(v___x_210_, v_size_168_);
lean_dec(v___x_210_);
lean_inc_ref(v_l_142_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 4, v_l_155_);
lean_ctor_set(v___x_166_, 3, v_l_142_);
lean_ctor_set(v___x_166_, 2, v_v_141_);
lean_ctor_set(v___x_166_, 1, v_k_140_);
lean_ctor_set(v___x_166_, 0, v___x_212_);
v___x_214_ = v___x_166_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_l_142_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_l_155_);
v___x_214_ = v_reuseFailAlloc_227_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v_isSharedCheck_221_ = !lean_is_exclusive(v_l_142_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; lean_object* v_unused_223_; lean_object* v_unused_224_; lean_object* v_unused_225_; lean_object* v_unused_226_; 
v_unused_222_ = lean_ctor_get(v_l_142_, 4);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_l_142_, 3);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_l_142_, 2);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_l_142_, 1);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_l_142_, 0);
lean_dec(v_unused_226_);
v___x_216_ = v_l_142_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_dec(v_l_142_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 4, v_r_156_);
lean_ctor_set(v___x_216_, 3, v___x_214_);
lean_ctor_set(v___x_216_, 2, v_v_154_);
lean_ctor_set(v___x_216_, 1, v_k_153_);
lean_ctor_set(v___x_216_, 0, v___x_211_);
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_k_153_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_v_154_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v_r_156_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_234_; 
v_l_234_ = lean_ctor_get(v_impl_149_, 3);
lean_inc(v_l_234_);
if (lean_obj_tag(v_l_234_) == 0)
{
lean_object* v_r_235_; lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_260_; 
v_r_235_ = lean_ctor_get(v_impl_149_, 4);
v_k_236_ = lean_ctor_get(v_impl_149_, 1);
v_v_237_ = lean_ctor_get(v_impl_149_, 2);
v_isSharedCheck_260_ = !lean_is_exclusive(v_impl_149_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; 
v_unused_261_ = lean_ctor_get(v_impl_149_, 3);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_impl_149_, 0);
lean_dec(v_unused_262_);
v___x_239_ = v_impl_149_;
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_r_235_);
lean_inc(v_v_237_);
lean_inc(v_k_236_);
lean_dec(v_impl_149_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_k_241_; lean_object* v_v_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_256_; 
v_k_241_ = lean_ctor_get(v_l_234_, 1);
v_v_242_ = lean_ctor_get(v_l_234_, 2);
v_isSharedCheck_256_ = !lean_is_exclusive(v_l_234_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; 
v_unused_257_ = lean_ctor_get(v_l_234_, 4);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_l_234_, 3);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_l_234_, 0);
lean_dec(v_unused_259_);
v___x_244_ = v_l_234_;
v_isShared_245_ = v_isSharedCheck_256_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_v_242_);
lean_inc(v_k_241_);
lean_dec(v_l_234_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_256_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_235_, 2);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 4, v_r_235_);
lean_ctor_set(v___x_244_, 3, v_r_235_);
lean_ctor_set(v___x_244_, 2, v_v_141_);
lean_ctor_set(v___x_244_, 1, v_k_140_);
lean_ctor_set(v___x_244_, 0, v___x_150_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_r_235_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_r_235_);
v___x_248_ = v_reuseFailAlloc_255_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
lean_inc(v_r_235_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 3, v_r_235_);
lean_ctor_set(v___x_239_, 0, v___x_150_);
v___x_250_ = v___x_239_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_236_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_237_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v_r_235_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v_r_235_);
v___x_250_ = v_reuseFailAlloc_254_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v___x_250_);
lean_ctor_set(v___x_145_, 3, v___x_248_);
lean_ctor_set(v___x_145_, 2, v_v_242_);
lean_ctor_set(v___x_145_, 1, v_k_241_);
lean_ctor_set(v___x_145_, 0, v___x_246_);
v___x_252_ = v___x_145_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_k_241_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_v_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
}
else
{
lean_object* v_r_263_; 
v_r_263_ = lean_ctor_get(v_impl_149_, 4);
lean_inc(v_r_263_);
if (lean_obj_tag(v_r_263_) == 0)
{
lean_object* v_k_264_; lean_object* v_v_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_276_; 
v_k_264_ = lean_ctor_get(v_impl_149_, 1);
v_v_265_ = lean_ctor_get(v_impl_149_, 2);
v_isSharedCheck_276_ = !lean_is_exclusive(v_impl_149_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; lean_object* v_unused_278_; lean_object* v_unused_279_; 
v_unused_277_ = lean_ctor_get(v_impl_149_, 4);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_impl_149_, 3);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_impl_149_, 0);
lean_dec(v_unused_279_);
v___x_267_ = v_impl_149_;
v_isShared_268_ = v_isSharedCheck_276_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_v_265_);
lean_inc(v_k_264_);
lean_dec(v_impl_149_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_276_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_unsigned_to_nat(3u);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 4, v_l_234_);
lean_ctor_set(v___x_267_, 2, v_v_141_);
lean_ctor_set(v___x_267_, 1, v_k_140_);
lean_ctor_set(v___x_267_, 0, v___x_150_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_l_234_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_l_234_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_r_263_);
lean_ctor_set(v___x_145_, 3, v___x_271_);
lean_ctor_set(v___x_145_, 2, v_v_265_);
lean_ctor_set(v___x_145_, 1, v_k_264_);
lean_ctor_set(v___x_145_, 0, v___x_269_);
v___x_273_ = v___x_145_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v_r_263_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_unsigned_to_nat(2u);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_impl_149_);
lean_ctor_set(v___x_145_, 3, v_r_263_);
lean_ctor_set(v___x_145_, 0, v___x_280_);
v___x_282_ = v___x_145_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_r_263_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_impl_149_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
else
{
lean_object* v___x_285_; 
lean_dec(v_v_141_);
lean_dec(v_k_140_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 2, v_v_137_);
lean_ctor_set(v___x_145_, 1, v_k_136_);
v___x_285_ = v___x_145_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_size_139_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_k_136_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_v_137_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_l_142_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_r_143_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
else
{
lean_object* v_impl_287_; lean_object* v___x_288_; 
lean_dec(v_size_139_);
v_impl_287_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_k_136_, v_v_137_, v_l_142_);
v___x_288_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_143_) == 0)
{
lean_object* v_size_289_; lean_object* v_size_290_; lean_object* v_k_291_; lean_object* v_v_292_; lean_object* v_l_293_; lean_object* v_r_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_size_289_ = lean_ctor_get(v_r_143_, 0);
v_size_290_ = lean_ctor_get(v_impl_287_, 0);
v_k_291_ = lean_ctor_get(v_impl_287_, 1);
v_v_292_ = lean_ctor_get(v_impl_287_, 2);
v_l_293_ = lean_ctor_get(v_impl_287_, 3);
v_r_294_ = lean_ctor_get(v_impl_287_, 4);
lean_inc(v_r_294_);
v___x_295_ = lean_unsigned_to_nat(3u);
v___x_296_ = lean_nat_mul(v___x_295_, v_size_289_);
v___x_297_ = lean_nat_dec_lt(v___x_296_, v_size_290_);
lean_dec(v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
lean_dec(v_r_294_);
v___x_298_ = lean_nat_add(v___x_288_, v_size_290_);
v___x_299_ = lean_nat_add(v___x_298_, v_size_289_);
lean_dec(v___x_298_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 3, v_impl_287_);
lean_ctor_set(v___x_145_, 0, v___x_299_);
v___x_301_ = v___x_145_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_impl_287_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v_r_143_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
else
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_368_; 
lean_inc(v_l_293_);
lean_inc(v_v_292_);
lean_inc(v_k_291_);
lean_inc(v_size_290_);
v_isSharedCheck_368_ = !lean_is_exclusive(v_impl_287_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_369_ = lean_ctor_get(v_impl_287_, 4);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_impl_287_, 3);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_impl_287_, 2);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_impl_287_, 1);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_impl_287_, 0);
lean_dec(v_unused_373_);
v___x_304_ = v_impl_287_;
v_isShared_305_ = v_isSharedCheck_368_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_impl_287_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_368_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_size_306_; lean_object* v_size_307_; lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v_l_310_; lean_object* v_r_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_size_306_ = lean_ctor_get(v_l_293_, 0);
v_size_307_ = lean_ctor_get(v_r_294_, 0);
v_k_308_ = lean_ctor_get(v_r_294_, 1);
v_v_309_ = lean_ctor_get(v_r_294_, 2);
v_l_310_ = lean_ctor_get(v_r_294_, 3);
v_r_311_ = lean_ctor_get(v_r_294_, 4);
v___x_312_ = lean_unsigned_to_nat(2u);
v___x_313_ = lean_nat_mul(v___x_312_, v_size_306_);
v___x_314_ = lean_nat_dec_lt(v_size_307_, v___x_313_);
lean_dec(v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_343_; 
lean_inc(v_r_311_);
lean_inc(v_l_310_);
lean_inc(v_v_309_);
lean_inc(v_k_308_);
v_isSharedCheck_343_ = !lean_is_exclusive(v_r_294_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; lean_object* v_unused_348_; 
v_unused_344_ = lean_ctor_get(v_r_294_, 4);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_r_294_, 3);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_r_294_, 2);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_r_294_, 1);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_r_294_, 0);
lean_dec(v_unused_348_);
v___x_316_ = v_r_294_;
v_isShared_317_ = v_isSharedCheck_343_;
goto v_resetjp_315_;
}
else
{
lean_dec(v_r_294_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_343_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___x_331_; lean_object* v___y_333_; 
v___x_318_ = lean_nat_add(v___x_288_, v_size_290_);
lean_dec(v_size_290_);
v___x_319_ = lean_nat_add(v___x_318_, v_size_289_);
lean_dec(v___x_318_);
v___x_331_ = lean_nat_add(v___x_288_, v_size_306_);
if (lean_obj_tag(v_l_310_) == 0)
{
lean_object* v_size_341_; 
v_size_341_ = lean_ctor_get(v_l_310_, 0);
lean_inc(v_size_341_);
v___y_333_ = v_size_341_;
goto v___jp_332_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v___y_333_ = v___x_342_;
goto v___jp_332_;
}
v___jp_320_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = lean_nat_add(v___y_321_, v___y_323_);
lean_dec(v___y_323_);
lean_dec(v___y_321_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 4, v_r_143_);
lean_ctor_set(v___x_316_, 3, v_r_311_);
lean_ctor_set(v___x_316_, 2, v_v_141_);
lean_ctor_set(v___x_316_, 1, v_k_140_);
lean_ctor_set(v___x_316_, 0, v___x_324_);
v___x_326_ = v___x_316_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_r_311_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_r_143_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 4, v___x_326_);
lean_ctor_set(v___x_304_, 3, v___y_322_);
lean_ctor_set(v___x_304_, 2, v_v_309_);
lean_ctor_set(v___x_304_, 1, v_k_308_);
lean_ctor_set(v___x_304_, 0, v___x_319_);
v___x_328_ = v___x_304_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v___y_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_nat_add(v___x_331_, v___y_333_);
lean_dec(v___y_333_);
lean_dec(v___x_331_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_l_310_);
lean_ctor_set(v___x_145_, 3, v_l_293_);
lean_ctor_set(v___x_145_, 2, v_v_292_);
lean_ctor_set(v___x_145_, 1, v_k_291_);
lean_ctor_set(v___x_145_, 0, v___x_334_);
v___x_336_ = v___x_145_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_l_293_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v_l_310_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; 
v___x_337_ = lean_nat_add(v___x_288_, v_size_289_);
if (lean_obj_tag(v_r_311_) == 0)
{
lean_object* v_size_338_; 
v_size_338_ = lean_ctor_get(v_r_311_, 0);
lean_inc(v_size_338_);
v___y_321_ = v___x_337_;
v___y_322_ = v___x_336_;
v___y_323_ = v_size_338_;
goto v___jp_320_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___y_321_ = v___x_337_;
v___y_322_ = v___x_336_;
v___y_323_ = v___x_339_;
goto v___jp_320_;
}
}
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
lean_del_object(v___x_145_);
v___x_349_ = lean_nat_add(v___x_288_, v_size_290_);
lean_dec(v_size_290_);
v___x_350_ = lean_nat_add(v___x_349_, v_size_289_);
lean_dec(v___x_349_);
v___x_351_ = lean_nat_add(v___x_288_, v_size_289_);
v___x_352_ = lean_nat_add(v___x_351_, v_size_307_);
lean_dec(v___x_351_);
lean_inc_ref(v_r_143_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 4, v_r_143_);
lean_ctor_set(v___x_304_, 3, v_r_294_);
lean_ctor_set(v___x_304_, 2, v_v_141_);
lean_ctor_set(v___x_304_, 1, v_k_140_);
lean_ctor_set(v___x_304_, 0, v___x_352_);
v___x_354_ = v___x_304_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_r_294_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_r_143_);
v___x_354_ = v_reuseFailAlloc_367_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
v_isSharedCheck_361_ = !lean_is_exclusive(v_r_143_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; lean_object* v_unused_363_; lean_object* v_unused_364_; lean_object* v_unused_365_; lean_object* v_unused_366_; 
v_unused_362_ = lean_ctor_get(v_r_143_, 4);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_r_143_, 3);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_r_143_, 2);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_r_143_, 1);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_r_143_, 0);
lean_dec(v_unused_366_);
v___x_356_ = v_r_143_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_dec(v_r_143_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 4, v___x_354_);
lean_ctor_set(v___x_356_, 3, v_l_293_);
lean_ctor_set(v___x_356_, 2, v_v_292_);
lean_ctor_set(v___x_356_, 1, v_k_291_);
lean_ctor_set(v___x_356_, 0, v___x_350_);
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_k_291_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_v_292_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_l_293_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v___x_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_374_; 
v_l_374_ = lean_ctor_get(v_impl_287_, 3);
if (lean_obj_tag(v_l_374_) == 0)
{
lean_object* v_r_375_; lean_object* v_k_376_; lean_object* v_v_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_388_; 
lean_inc_ref(v_l_374_);
v_r_375_ = lean_ctor_get(v_impl_287_, 4);
v_k_376_ = lean_ctor_get(v_impl_287_, 1);
v_v_377_ = lean_ctor_get(v_impl_287_, 2);
v_isSharedCheck_388_ = !lean_is_exclusive(v_impl_287_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; lean_object* v_unused_390_; 
v_unused_389_ = lean_ctor_get(v_impl_287_, 3);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_impl_287_, 0);
lean_dec(v_unused_390_);
v___x_379_ = v_impl_287_;
v_isShared_380_ = v_isSharedCheck_388_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_r_375_);
lean_inc(v_v_377_);
lean_inc(v_k_376_);
lean_dec(v_impl_287_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_388_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_375_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 3, v_r_375_);
lean_ctor_set(v___x_379_, 2, v_v_141_);
lean_ctor_set(v___x_379_, 1, v_k_140_);
lean_ctor_set(v___x_379_, 0, v___x_288_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v_r_375_);
lean_ctor_set(v_reuseFailAlloc_387_, 4, v_r_375_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_385_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v___x_383_);
lean_ctor_set(v___x_145_, 3, v_l_374_);
lean_ctor_set(v___x_145_, 2, v_v_377_);
lean_ctor_set(v___x_145_, 1, v_k_376_);
lean_ctor_set(v___x_145_, 0, v___x_381_);
v___x_385_ = v___x_145_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_k_376_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_v_377_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_l_374_);
lean_ctor_set(v_reuseFailAlloc_386_, 4, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v_r_391_; 
v_r_391_ = lean_ctor_get(v_impl_287_, 4);
lean_inc(v_r_391_);
if (lean_obj_tag(v_r_391_) == 0)
{
lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_416_; 
lean_inc(v_l_374_);
v_k_392_ = lean_ctor_get(v_impl_287_, 1);
v_v_393_ = lean_ctor_get(v_impl_287_, 2);
v_isSharedCheck_416_ = !lean_is_exclusive(v_impl_287_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; lean_object* v_unused_418_; lean_object* v_unused_419_; 
v_unused_417_ = lean_ctor_get(v_impl_287_, 4);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_impl_287_, 3);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_impl_287_, 0);
lean_dec(v_unused_419_);
v___x_395_ = v_impl_287_;
v_isShared_396_ = v_isSharedCheck_416_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_v_393_);
lean_inc(v_k_392_);
lean_dec(v_impl_287_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_416_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_k_397_; lean_object* v_v_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_412_; 
v_k_397_ = lean_ctor_get(v_r_391_, 1);
v_v_398_ = lean_ctor_get(v_r_391_, 2);
v_isSharedCheck_412_ = !lean_is_exclusive(v_r_391_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_413_ = lean_ctor_get(v_r_391_, 4);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_r_391_, 3);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_r_391_, 0);
lean_dec(v_unused_415_);
v___x_400_ = v_r_391_;
v_isShared_401_ = v_isSharedCheck_412_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_v_398_);
lean_inc(v_k_397_);
lean_dec(v_r_391_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_412_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(3u);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 4, v_l_374_);
lean_ctor_set(v___x_400_, 3, v_l_374_);
lean_ctor_set(v___x_400_, 2, v_v_393_);
lean_ctor_set(v___x_400_, 1, v_k_392_);
lean_ctor_set(v___x_400_, 0, v___x_288_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_k_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_v_393_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_l_374_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_l_374_);
v___x_404_ = v_reuseFailAlloc_411_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 4, v_l_374_);
lean_ctor_set(v___x_395_, 2, v_v_141_);
lean_ctor_set(v___x_395_, 1, v_k_140_);
lean_ctor_set(v___x_395_, 0, v___x_288_);
v___x_406_ = v___x_395_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_l_374_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_l_374_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v___x_406_);
lean_ctor_set(v___x_145_, 3, v___x_404_);
lean_ctor_set(v___x_145_, 2, v_v_398_);
lean_ctor_set(v___x_145_, 1, v_k_397_);
lean_ctor_set(v___x_145_, 0, v___x_402_);
v___x_408_ = v___x_145_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v___x_406_);
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
else
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(2u);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_r_391_);
lean_ctor_set(v___x_145_, 3, v_impl_287_);
lean_ctor_set(v___x_145_, 0, v___x_420_);
v___x_422_ = v___x_145_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_impl_287_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_r_391_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_k_136_);
lean_ctor_set(v___x_426_, 2, v_v_137_);
lean_ctor_set(v___x_426_, 3, v_t_138_);
lean_ctor_set(v___x_426_, 4, v_t_138_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* v_x_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_foundJPs_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_444_; lean_object* v___x_451_; lean_object* v_foundVars_452_; uint8_t v___x_453_; 
v___x_451_ = lean_st_ref_get(v_a_431_);
v_foundVars_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_foundVars_452_);
lean_dec(v___x_451_);
v___x_453_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_x_429_, v_foundVars_452_);
lean_dec(v_foundVars_452_);
if (v___x_453_ == 0)
{
v___y_444_ = v_a_431_;
goto v___jp_443_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_454_ = ((lean_object*)(l_Lean_IR_Checker_markVar___closed__0));
v___x_455_ = l_Nat_reprFast(v_x_429_);
v___x_456_ = lean_string_append(v___x_454_, v___x_455_);
lean_dec_ref(v___x_455_);
v___x_457_ = ((lean_object*)(l_Lean_IR_Checker_markVar___closed__1));
v___x_458_ = lean_string_append(v___x_456_, v___x_457_);
v___x_459_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_458_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
return v___x_459_;
}
v___jp_435_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___y_439_);
lean_ctor_set(v___x_440_, 1, v_foundJPs_436_);
v___x_441_ = lean_st_ref_put(v___y_438_, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___y_437_);
return v___x_442_;
}
v___jp_443_:
{
lean_object* v___x_445_; lean_object* v_foundVars_446_; lean_object* v_foundJPs_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_445_ = lean_st_ref_take(v___y_444_);
v_foundVars_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_foundVars_446_);
v_foundJPs_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_foundJPs_447_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v___x_449_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_x_429_, v_foundVars_446_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_x_429_, v___x_448_, v_foundVars_446_);
v_foundJPs_436_ = v_foundJPs_447_;
v___y_437_ = v___x_448_;
v___y_438_ = v___y_444_;
v___y_439_ = v___x_450_;
goto v___jp_435_;
}
else
{
lean_dec(v_x_429_);
v_foundJPs_436_ = v_foundJPs_447_;
v___y_437_ = v___x_448_;
v___y_438_ = v___y_444_;
v___y_439_ = v_foundVars_446_;
goto v___jp_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* v_x_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_IR_Checker_markVar(v_x_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_466_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0(lean_object* v_00_u03b2_467_, lean_object* v_k_468_, lean_object* v_t_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_k_468_, v_t_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___boxed(lean_object* v_00_u03b2_471_, lean_object* v_k_472_, lean_object* v_t_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0(v_00_u03b2_471_, v_k_472_, v_t_473_);
lean_dec(v_t_473_);
lean_dec(v_k_472_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1(lean_object* v_00_u03b2_476_, lean_object* v_k_477_, lean_object* v_v_478_, lean_object* v_t_479_, lean_object* v_hl_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_k_477_, v_v_478_, v_t_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* v_j_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_498_; lean_object* v___x_505_; lean_object* v_foundJPs_506_; uint8_t v___x_507_; 
v___x_505_ = lean_st_ref_get(v_a_485_);
v_foundJPs_506_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_foundJPs_506_);
lean_dec(v___x_505_);
v___x_507_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_j_483_, v_foundJPs_506_);
lean_dec(v_foundJPs_506_);
if (v___x_507_ == 0)
{
v___y_498_ = v_a_485_;
goto v___jp_497_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_508_ = ((lean_object*)(l_Lean_IR_Checker_markJP___closed__0));
v___x_509_ = l_Nat_reprFast(v_j_483_);
v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
lean_dec_ref(v___x_509_);
v___x_511_ = ((lean_object*)(l_Lean_IR_Checker_markVar___closed__1));
v___x_512_ = lean_string_append(v___x_510_, v___x_511_);
v___x_513_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_512_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
return v___x_513_;
}
v___jp_489_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___y_491_);
lean_ctor_set(v___x_494_, 1, v___y_493_);
v___x_495_ = lean_st_ref_put(v___y_492_, v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___y_490_);
return v___x_496_;
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v_foundVars_500_; lean_object* v_foundJPs_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_499_ = lean_st_ref_take(v___y_498_);
v_foundVars_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_foundVars_500_);
v_foundJPs_501_ = lean_ctor_get(v___x_499_, 1);
lean_inc(v_foundJPs_501_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v___x_503_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markVar_spec__0___redArg(v_j_483_, v_foundJPs_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markVar_spec__1___redArg(v_j_483_, v___x_502_, v_foundJPs_501_);
v___y_490_ = v___x_502_;
v___y_491_ = v_foundVars_500_;
v___y_492_ = v___y_498_;
v___y_493_ = v___x_504_;
goto v___jp_489_;
}
else
{
lean_dec(v_j_483_);
v___y_490_ = v___x_502_;
v___y_491_ = v_foundVars_500_;
v___y_492_ = v___y_498_;
v___y_493_ = v_foundJPs_501_;
goto v___jp_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* v_j_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_IR_Checker_markJP(v_j_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_521_, lean_object* v_vals_522_, lean_object* v_i_523_, lean_object* v_k_524_){
_start:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_array_get_size(v_keys_521_);
v___x_526_ = lean_nat_dec_lt(v_i_523_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_dec(v_i_523_);
v___x_527_ = lean_box(0);
return v___x_527_;
}
else
{
lean_object* v_k_x27_528_; uint8_t v___x_529_; 
v_k_x27_528_ = lean_array_fget_borrowed(v_keys_521_, v_i_523_);
v___x_529_ = lean_name_eq(v_k_524_, v_k_x27_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_i_523_, v___x_530_);
lean_dec(v_i_523_);
v_i_523_ = v___x_531_;
goto _start;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_array_fget_borrowed(v_vals_522_, v_i_523_);
lean_dec(v_i_523_);
lean_inc(v___x_533_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_535_, lean_object* v_vals_536_, lean_object* v_i_537_, lean_object* v_k_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(v_keys_535_, v_vals_536_, v_i_537_, v_k_538_);
lean_dec(v_k_538_);
lean_dec_ref(v_vals_536_);
lean_dec_ref(v_keys_535_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(lean_object* v_x_540_, size_t v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v_es_543_; lean_object* v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v_j_547_; lean_object* v___x_548_; 
v_es_543_ = lean_ctor_get(v_x_540_, 0);
v___x_544_ = lean_box(2);
v___x_545_ = ((size_t)31ULL);
v___x_546_ = lean_usize_land(v_x_541_, v___x_545_);
v_j_547_ = lean_usize_to_nat(v___x_546_);
v___x_548_ = lean_array_get_borrowed(v___x_544_, v_es_543_, v_j_547_);
lean_dec(v_j_547_);
switch(lean_obj_tag(v___x_548_))
{
case 0:
{
lean_object* v_key_549_; lean_object* v_val_550_; uint8_t v___x_551_; 
v_key_549_ = lean_ctor_get(v___x_548_, 0);
v_val_550_ = lean_ctor_get(v___x_548_, 1);
v___x_551_ = lean_name_eq(v_x_542_, v_key_549_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_box(0);
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
lean_inc(v_val_550_);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_val_550_);
return v___x_553_;
}
}
case 1:
{
lean_object* v_node_554_; size_t v___x_555_; size_t v___x_556_; 
v_node_554_ = lean_ctor_get(v___x_548_, 0);
v___x_555_ = ((size_t)5ULL);
v___x_556_ = lean_usize_shift_right(v_x_541_, v___x_555_);
v_x_540_ = v_node_554_;
v_x_541_ = v___x_556_;
goto _start;
}
default: 
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
}
else
{
lean_object* v_ks_559_; lean_object* v_vs_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_ks_559_ = lean_ctor_get(v_x_540_, 0);
v_vs_560_ = lean_ctor_get(v_x_540_, 1);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(v_ks_559_, v_vs_560_, v___x_561_, v_x_542_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
size_t v_x_1166__boxed_566_; lean_object* v_res_567_; 
v_x_1166__boxed_566_ = lean_unbox_usize(v_x_564_);
lean_dec(v_x_564_);
v_res_567_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(v_x_563_, v_x_1166__boxed_566_, v_x_565_);
lean_dec(v_x_565_);
lean_dec_ref(v_x_563_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
uint64_t v___y_571_; 
if (lean_obj_tag(v_x_569_) == 0)
{
uint64_t v___x_574_; 
v___x_574_ = 1723ULL;
v___y_571_ = v___x_574_;
goto v___jp_570_;
}
else
{
uint64_t v_hash_575_; 
v_hash_575_ = lean_ctor_get_uint64(v_x_569_, sizeof(void*)*2);
v___y_571_ = v_hash_575_;
goto v___jp_570_;
}
v___jp_570_:
{
size_t v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_uint64_to_usize(v___y_571_);
v___x_573_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(v_x_568_, v___x_572_, v_x_569_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg___boxed(lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(v_x_576_, v_x_577_);
lean_dec(v_x_577_);
lean_dec_ref(v_x_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* v_c_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_587_; lean_object* v_decls_588_; lean_object* v___x_589_; 
v___x_587_ = lean_st_ref_get(v_a_585_);
v_decls_588_ = lean_ctor_get(v_a_582_, 2);
v___x_589_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(v_decls_588_, v_c_581_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_env_590_; lean_object* v___x_591_; 
v_env_590_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_587_);
lean_inc(v_c_581_);
v___x_591_ = l_Lean_IR_findEnvDecl(v_env_590_, v_c_581_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_592_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
v___x_593_ = 1;
v___x_594_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_581_, v___x_593_);
v___x_595_ = lean_string_append(v___x_592_, v___x_594_);
lean_dec_ref(v___x_594_);
v___x_596_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
v___x_598_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_597_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
return v___x_598_;
}
else
{
lean_object* v_val_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_c_581_);
v_val_599_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_591_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_val_599_);
lean_dec(v___x_591_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 0);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_val_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec(v___x_587_);
lean_dec(v_c_581_);
v_val_607_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_589_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v___x_589_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 0);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_val_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* v_c_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_IR_Checker_getDecl(v_c_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0(lean_object* v_00_u03b2_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(v_x_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___boxed(lean_object* v_00_u03b2_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0(v_00_u03b2_626_, v_x_627_, v_x_628_);
lean_dec(v_x_628_);
lean_dec_ref(v_x_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0(lean_object* v_00_u03b2_630_, lean_object* v_x_631_, size_t v_x_632_, lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(v_x_631_, v_x_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
size_t v_x_1298__boxed_639_; lean_object* v_res_640_; 
v_x_1298__boxed_639_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_640_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0(v_00_u03b2_635_, v_x_636_, v_x_1298__boxed_639_, v_x_638_);
lean_dec(v_x_638_);
lean_dec_ref(v_x_636_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_641_, lean_object* v_keys_642_, lean_object* v_vals_643_, lean_object* v_heq_644_, lean_object* v_i_645_, lean_object* v_k_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(v_keys_642_, v_vals_643_, v_i_645_, v_k_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_648_, lean_object* v_keys_649_, lean_object* v_vals_650_, lean_object* v_heq_651_, lean_object* v_i_652_, lean_object* v_k_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1(v_00_u03b2_648_, v_keys_649_, v_vals_650_, v_heq_651_, v_i_652_, v_k_653_);
lean_dec(v_k_653_);
lean_dec_ref(v_vals_650_);
lean_dec_ref(v_keys_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* v_x_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_localCtx_667_; uint8_t v___x_668_; 
v_localCtx_667_ = lean_ctor_get(v_a_659_, 0);
v___x_668_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_667_, v_x_658_);
if (v___x_668_ == 0)
{
uint8_t v___x_669_; 
v___x_669_ = l_Lean_IR_LocalContext_isParam(v_localCtx_667_, v_x_658_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_670_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_671_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_672_ = l_Nat_reprFast(v_x_658_);
v___x_673_ = lean_string_append(v___x_671_, v___x_672_);
lean_dec_ref(v___x_672_);
v___x_674_ = lean_string_append(v___x_670_, v___x_673_);
lean_dec_ref(v___x_673_);
v___x_675_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
v___x_677_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_676_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
return v___x_677_;
}
else
{
lean_dec(v_x_658_);
goto v___jp_664_;
}
}
else
{
lean_dec(v_x_658_);
goto v___jp_664_;
}
v___jp_664_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(0);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_IR_Checker_checkVar(v_x_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_localCtx_693_; uint8_t v___x_694_; 
v_localCtx_693_ = lean_ctor_get(v_a_688_, 0);
v___x_694_ = l_Lean_IR_LocalContext_isJP(v_localCtx_693_, v_j_687_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_695_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_696_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_697_ = l_Nat_reprFast(v_j_687_);
v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
lean_dec_ref(v___x_697_);
v___x_699_ = lean_string_append(v___x_695_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
v___x_702_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_701_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_j_687_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_IR_Checker_checkJP(v_j_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
if (lean_obj_tag(v_a_712_) == 0)
{
lean_object* v_id_718_; lean_object* v___x_719_; 
v_id_718_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_id_718_);
lean_dec_ref_known(v_a_712_, 1);
v___x_719_ = l_Lean_IR_Checker_checkVar(v_id_718_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_IR_Checker_checkArg(v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_729_, size_t v_i_730_, size_t v_stop_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_eq(v_i_730_, v_stop_731_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_array_uget_borrowed(v_as_729_, v_i_730_);
lean_inc(v___x_739_);
v___x_740_ = l_Lean_IR_Checker_checkArg(v___x_739_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; size_t v___x_742_; size_t v___x_743_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_730_, v___x_742_);
v_i_730_ = v___x_743_;
v_b_732_ = v_a_741_;
goto _start;
}
else
{
return v___x_740_;
}
}
else
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_b_732_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_746_, lean_object* v_i_747_, lean_object* v_stop_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
size_t v_i_boxed_755_; size_t v_stop_boxed_756_; lean_object* v_res_757_; 
v_i_boxed_755_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_stop_boxed_756_ = lean_unbox_usize(v_stop_748_);
lean_dec(v_stop_748_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_746_, v_i_boxed_755_, v_stop_boxed_756_, v_b_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec_ref(v_as_746_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_array_get_size(v_as_758_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
return v___x_768_;
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_of_nat(v___x_765_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_758_, v___x_769_, v___x_770_, v___x_766_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_IR_Checker_checkArgs(v_as_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec_ref(v_as_772_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_780_, lean_object* v_ty_u2082_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_780_, v_ty_u2082_781_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_789_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_788_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_box(0);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_792_, lean_object* v_ty_u2082_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_792_, v_ty_u2082_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_ty_u2082_793_);
lean_dec(v_ty_u2081_792_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_802_, lean_object* v_p_803_, lean_object* v_suffix_x3f_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___x_810_; uint8_t v___x_811_; 
lean_inc(v_ty_802_);
v___x_810_ = lean_apply_1(v_p_803_, v_ty_802_);
v___x_811_ = lean_unbox(v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_msg_819_; 
v___x_812_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_813_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_802_);
v___x_814_ = l_Std_Format_defWidth;
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = l_Std_Format_pretty(v___x_813_, v___x_814_, v___x_815_, v___x_815_);
v___x_817_ = lean_string_append(v___x_812_, v___x_816_);
lean_dec_ref(v___x_816_);
v___x_818_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_819_ = lean_string_append(v___x_817_, v___x_818_);
if (lean_obj_tag(v_suffix_x3f_804_) == 1)
{
lean_object* v_val_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_msg_823_; lean_object* v___x_824_; 
v_val_820_ = lean_ctor_get(v_suffix_x3f_804_, 0);
v___x_821_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_822_ = lean_string_append(v_msg_819_, v___x_821_);
v_msg_823_ = lean_string_append(v___x_822_, v_val_820_);
v___x_824_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_823_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
return v___x_824_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_819_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
return v___x_825_;
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec(v_ty_802_);
v___x_826_ = lean_box(0);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_828_, lean_object* v_p_829_, lean_object* v_suffix_x3f_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_IR_Checker_checkType(v_ty_828_, v_p_829_, v_suffix_x3f_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_suffix_x3f_830_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_IR_IRType_isObj(v_ty_838_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_msg_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_msg_856_; lean_object* v___x_857_; 
v___x_845_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_846_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_847_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_838_);
v___x_848_ = l_Std_Format_defWidth;
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = l_Std_Format_pretty(v___x_847_, v___x_848_, v___x_849_, v___x_849_);
v___x_851_ = lean_string_append(v___x_846_, v___x_850_);
lean_dec_ref(v___x_850_);
v___x_852_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_853_ = lean_string_append(v___x_851_, v___x_852_);
v___x_854_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_855_ = lean_string_append(v_msg_853_, v___x_854_);
v_msg_856_ = lean_string_append(v___x_855_, v___x_845_);
v___x_857_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_856_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_ty_838_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_IR_Checker_checkObjType(v_ty_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_IR_IRType_isScalar(v_ty_868_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_msg_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_msg_886_; lean_object* v___x_887_; 
v___x_875_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_876_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_877_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_868_);
v___x_878_ = l_Std_Format_defWidth;
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = l_Std_Format_pretty(v___x_877_, v___x_878_, v___x_879_, v___x_879_);
v___x_881_ = lean_string_append(v___x_876_, v___x_880_);
lean_dec_ref(v___x_880_);
v___x_882_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_883_ = lean_string_append(v___x_881_, v___x_882_);
v___x_884_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_885_ = lean_string_append(v_msg_883_, v___x_884_);
v_msg_886_ = lean_string_append(v___x_885_, v___x_875_);
v___x_887_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_886_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_ty_868_);
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_IR_Checker_checkScalarType(v_ty_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_localCtx_903_; lean_object* v___x_904_; 
v_localCtx_903_ = lean_ctor_get(v_a_898_, 0);
v___x_904_ = l_Lean_IR_LocalContext_getType(v_localCtx_903_, v_x_897_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_905_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_906_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_907_ = l_Nat_reprFast(v_x_897_);
v___x_908_ = lean_string_append(v___x_906_, v___x_907_);
lean_dec_ref(v___x_907_);
v___x_909_ = lean_string_append(v___x_905_, v___x_908_);
lean_dec_ref(v___x_908_);
v___x_910_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_911_ = lean_string_append(v___x_909_, v___x_910_);
v___x_912_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_911_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_912_;
}
else
{
lean_object* v_val_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_x_897_);
v_val_913_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_904_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_val_913_);
lean_dec(v___x_904_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set_tag(v___x_915_, 0);
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_val_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_IR_Checker_getType(v_x_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_928_, lean_object* v_p_929_, lean_object* v_suffix_x3f_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_IR_Checker_getType(v_x_928_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_961_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_961_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_961_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_961_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; uint8_t v___x_942_; 
lean_inc(v_a_937_);
v___x_941_ = lean_apply_1(v_p_929_, v_a_937_);
v___x_942_ = lean_unbox(v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_msg_950_; 
lean_del_object(v___x_939_);
v___x_943_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_944_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_937_);
v___x_945_ = l_Std_Format_defWidth;
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = l_Std_Format_pretty(v___x_944_, v___x_945_, v___x_946_, v___x_946_);
v___x_948_ = lean_string_append(v___x_943_, v___x_947_);
lean_dec_ref(v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_950_ = lean_string_append(v___x_948_, v___x_949_);
if (lean_obj_tag(v_suffix_x3f_930_) == 1)
{
lean_object* v_val_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_msg_954_; lean_object* v___x_955_; 
v_val_951_ = lean_ctor_get(v_suffix_x3f_930_, 0);
v___x_952_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_953_ = lean_string_append(v_msg_950_, v___x_952_);
v_msg_954_ = lean_string_append(v___x_953_, v_val_951_);
v___x_955_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_954_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_950_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
return v___x_956_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_959_; 
lean_dec(v_a_937_);
v___x_957_ = lean_box(0);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_957_);
v___x_959_ = v___x_939_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v_p_929_);
v_a_962_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_936_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_936_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_970_, lean_object* v_p_971_, lean_object* v_suffix_x3f_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_IR_Checker_checkVarType(v_x_970_, v_p_971_, v_suffix_x3f_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_suffix_x3f_972_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_986_ = l_Lean_IR_Checker_getType(v_x_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1008_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1008_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1008_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_IR_IRType_isObj(v_a_987_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v_msg_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_msg_1002_; lean_object* v___x_1003_; 
lean_del_object(v___x_989_);
v___x_992_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_993_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_987_);
v___x_994_ = l_Std_Format_defWidth;
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = l_Std_Format_pretty(v___x_993_, v___x_994_, v___x_995_, v___x_995_);
v___x_997_ = lean_string_append(v___x_992_, v___x_996_);
lean_dec_ref(v___x_996_);
v___x_998_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_999_ = lean_string_append(v___x_997_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_1001_ = lean_string_append(v_msg_999_, v___x_1000_);
v_msg_1002_ = lean_string_append(v___x_1001_, v___x_985_);
v___x_1003_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1002_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_1003_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
lean_dec(v_a_987_);
v___x_1004_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_1004_);
v___x_1006_ = v___x_989_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_986_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_986_);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_IR_Checker_checkObjVar(v_x_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_1031_ = l_Lean_IR_Checker_getType(v_x_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1053_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1053_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1053_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
uint8_t v___x_1036_; 
v___x_1036_ = l_Lean_IR_IRType_isScalar(v_a_1032_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_msg_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_msg_1047_; lean_object* v___x_1048_; 
lean_del_object(v___x_1034_);
v___x_1037_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1038_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1032_);
v___x_1039_ = l_Std_Format_defWidth;
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = l_Std_Format_pretty(v___x_1038_, v___x_1039_, v___x_1040_, v___x_1040_);
v___x_1042_ = lean_string_append(v___x_1037_, v___x_1041_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1044_ = lean_string_append(v___x_1042_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_1046_ = lean_string_append(v_msg_1044_, v___x_1045_);
v_msg_1047_ = lean_string_append(v___x_1046_, v___x_1030_);
v___x_1048_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1047_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
lean_dec(v_a_1032_);
v___x_1049_ = lean_box(0);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1049_);
v___x_1051_ = v___x_1034_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1031_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1031_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_IR_Checker_checkScalarVar(v_x_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_1073_, lean_object* v_ys_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1080_; 
lean_inc(v_c_1073_);
v___x_1080_ = l_Lean_IR_Checker_getDecl(v_c_1073_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = lean_array_get_size(v_ys_1074_);
v___x_1083_ = l_Lean_IR_Decl_params(v_a_1081_);
lean_dec(v_a_1081_);
v___x_1084_ = lean_array_get_size(v___x_1083_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = lean_nat_dec_eq(v___x_1082_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1086_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_1087_ = 1;
v___x_1088_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1073_, v___x_1087_);
v___x_1089_ = lean_string_append(v___x_1086_, v___x_1088_);
lean_dec_ref(v___x_1088_);
v___x_1090_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_1091_ = lean_string_append(v___x_1089_, v___x_1090_);
v___x_1092_ = l_Nat_reprFast(v___x_1082_);
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_1095_ = lean_string_append(v___x_1093_, v___x_1094_);
v___x_1096_ = l_Nat_reprFast(v___x_1084_);
v___x_1097_ = lean_string_append(v___x_1095_, v___x_1096_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_1099_ = lean_string_append(v___x_1097_, v___x_1098_);
v___x_1100_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1099_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; 
lean_dec(v_c_1073_);
v___x_1101_ = l_Lean_IR_Checker_checkArgs(v_ys_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
return v___x_1101_;
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_c_1073_);
v_a_1102_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1080_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1080_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_1110_, lean_object* v_ys_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_IR_Checker_checkFullApp(v_c_1110_, v_ys_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec_ref(v_ys_1111_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1121_, lean_object* v_ys_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; 
lean_inc(v_c_1121_);
v___x_1128_ = l_Lean_IR_Checker_getDecl(v_c_1121_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = lean_array_get_size(v_ys_1122_);
v___x_1131_ = l_Lean_IR_Decl_params(v_a_1129_);
lean_dec(v_a_1129_);
v___x_1132_ = lean_array_get_size(v___x_1131_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = lean_nat_dec_lt(v___x_1130_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1134_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1135_ = 1;
v___x_1136_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1121_, v___x_1135_);
v___x_1137_ = lean_string_append(v___x_1134_, v___x_1136_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1139_ = lean_string_append(v___x_1137_, v___x_1138_);
v___x_1140_ = l_Nat_reprFast(v___x_1130_);
v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1143_ = lean_string_append(v___x_1141_, v___x_1142_);
v___x_1144_ = l_Nat_reprFast(v___x_1132_);
v___x_1145_ = lean_string_append(v___x_1143_, v___x_1144_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1145_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_c_1121_);
v___x_1147_ = l_Lean_IR_Checker_checkArgs(v_ys_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
return v___x_1147_;
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_c_1121_);
v_a_1148_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1128_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1128_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
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
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1156_, lean_object* v_ys_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_IR_Checker_checkPartialApp(v_c_1156_, v_ys_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec_ref(v_ys_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1171_, lean_object* v_e_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
switch(lean_obj_tag(v_e_1172_))
{
case 0:
{
lean_object* v_i_1178_; lean_object* v_ys_1179_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v_name_1190_; lean_object* v_cidx_1191_; lean_object* v_size_1192_; lean_object* v_usize_1193_; lean_object* v_ssize_1194_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_i_1178_ = lean_ctor_get(v_e_1172_, 0);
lean_inc_ref(v_i_1178_);
v_ys_1179_ = lean_ctor_get(v_e_1172_, 1);
lean_inc_ref(v_ys_1179_);
lean_dec_ref_known(v_e_1172_, 2);
v_name_1190_ = lean_ctor_get(v_i_1178_, 0);
v_cidx_1191_ = lean_ctor_get(v_i_1178_, 1);
v_size_1192_ = lean_ctor_get(v_i_1178_, 2);
v_usize_1193_ = lean_ctor_get(v_i_1178_, 3);
v_ssize_1194_ = lean_ctor_get(v_i_1178_, 4);
v___x_1224_ = l_Lean_maxCtorTag;
v___x_1225_ = lean_nat_dec_lt(v___x_1224_, v_cidx_1191_);
if (v___x_1225_ == 0)
{
v___y_1212_ = v_a_1173_;
v___y_1213_ = v_a_1174_;
v___y_1214_ = v_a_1175_;
v___y_1215_ = v_a_1176_;
goto v___jp_1211_;
}
else
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Lean_IR_CtorInfo_isRef(v_i_1178_);
if (v___x_1226_ == 0)
{
v___y_1212_ = v_a_1173_;
v___y_1213_ = v_a_1174_;
v___y_1214_ = v_a_1175_;
v___y_1215_ = v_a_1176_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_inc(v_name_1190_);
lean_dec_ref(v_ys_1179_);
lean_dec_ref(v_i_1178_);
lean_dec(v_ty_1171_);
v___x_1227_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1228_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1190_, v___x_1226_);
v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1231_ = lean_string_append(v___x_1229_, v___x_1230_);
v___x_1232_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1231_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1232_;
}
}
v___jp_1180_:
{
uint8_t v___x_1185_; 
v___x_1185_ = l_Lean_IR_CtorInfo_isRef(v_i_1178_);
lean_dec_ref(v_i_1178_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref(v_ys_1179_);
lean_dec(v_ty_1171_);
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref_known(v___x_1188_, 1);
v___x_1189_ = l_Lean_IR_Checker_checkArgs(v_ys_1179_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec_ref(v_ys_1179_);
return v___x_1189_;
}
else
{
lean_dec_ref(v_ys_1179_);
return v___x_1188_;
}
}
}
v___jp_1195_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1200_ = l_Lean_maxCtorScalarsSize;
v___x_1201_ = l_Lean_usizeSize;
v___x_1202_ = lean_nat_mul(v_usize_1193_, v___x_1201_);
v___x_1203_ = lean_nat_add(v_ssize_1194_, v___x_1202_);
lean_dec(v___x_1202_);
v___x_1204_ = lean_nat_dec_lt(v___x_1200_, v___x_1203_);
lean_dec(v___x_1203_);
if (v___x_1204_ == 0)
{
v___y_1181_ = v___y_1196_;
v___y_1182_ = v___y_1197_;
v___y_1183_ = v___y_1198_;
v___y_1184_ = v___y_1199_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_inc(v_name_1190_);
lean_dec_ref(v_ys_1179_);
lean_dec_ref(v_i_1178_);
lean_dec(v_ty_1171_);
v___x_1205_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1190_, v___x_1204_);
v___x_1207_ = lean_string_append(v___x_1205_, v___x_1206_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1209_ = lean_string_append(v___x_1207_, v___x_1208_);
v___x_1210_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1209_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1210_;
}
}
v___jp_1211_:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = l_Lean_maxCtorNumObjs;
v___x_1217_ = lean_nat_dec_lt(v___x_1216_, v_size_1192_);
if (v___x_1217_ == 0)
{
v___y_1196_ = v___y_1212_;
v___y_1197_ = v___y_1213_;
v___y_1198_ = v___y_1214_;
v___y_1199_ = v___y_1215_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_inc(v_name_1190_);
lean_dec_ref(v_ys_1179_);
lean_dec_ref(v_i_1178_);
lean_dec(v_ty_1171_);
v___x_1218_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1219_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1190_, v___x_1217_);
v___x_1220_ = lean_string_append(v___x_1218_, v___x_1219_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1222_ = lean_string_append(v___x_1220_, v___x_1221_);
v___x_1223_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1222_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
return v___x_1223_;
}
}
}
case 1:
{
lean_object* v_x_1233_; lean_object* v___x_1234_; 
v_x_1233_ = lean_ctor_get(v_e_1172_, 1);
lean_inc(v_x_1233_);
lean_dec_ref_known(v_e_1172_, 2);
v___x_1234_ = l_Lean_IR_Checker_checkObjVar(v_x_1233_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref_known(v___x_1234_, 1);
v___x_1235_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1235_;
}
else
{
lean_dec(v_ty_1171_);
return v___x_1234_;
}
}
case 2:
{
lean_object* v_x_1236_; lean_object* v_ys_1237_; lean_object* v___x_1238_; 
v_x_1236_ = lean_ctor_get(v_e_1172_, 0);
lean_inc(v_x_1236_);
v_ys_1237_ = lean_ctor_get(v_e_1172_, 2);
lean_inc_ref(v_ys_1237_);
lean_dec_ref_known(v_e_1172_, 3);
v___x_1238_ = l_Lean_IR_Checker_checkObjVar(v_x_1236_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref_known(v___x_1238_, 1);
v___x_1239_ = l_Lean_IR_Checker_checkArgs(v_ys_1237_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec_ref(v_ys_1237_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref_known(v___x_1239_, 1);
v___x_1240_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1240_;
}
else
{
lean_dec(v_ty_1171_);
return v___x_1239_;
}
}
else
{
lean_dec_ref(v_ys_1237_);
lean_dec(v_ty_1171_);
return v___x_1238_;
}
}
case 3:
{
lean_object* v_i_1241_; lean_object* v_x_1242_; lean_object* v___x_1243_; 
v_i_1241_ = lean_ctor_get(v_e_1172_, 0);
lean_inc(v_i_1241_);
v_x_1242_ = lean_ctor_get(v_e_1172_, 1);
lean_inc(v_x_1242_);
lean_dec_ref_known(v_e_1172_, 2);
v___x_1243_ = l_Lean_IR_Checker_getType(v_x_1242_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1289_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1289_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1289_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
switch(lean_obj_tag(v_a_1244_))
{
case 7:
{
lean_object* v___x_1248_; 
lean_del_object(v___x_1246_);
lean_dec(v_i_1241_);
v___x_1248_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1248_;
}
case 8:
{
lean_object* v___x_1249_; 
lean_del_object(v___x_1246_);
lean_dec(v_i_1241_);
v___x_1249_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1249_;
}
case 10:
{
lean_object* v_types_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_types_1250_ = lean_ctor_get(v_a_1244_, 1);
lean_inc_ref(v_types_1250_);
lean_dec_ref_known(v_a_1244_, 2);
v___x_1251_ = lean_array_get_size(v_types_1250_);
v___x_1252_ = lean_nat_dec_lt(v_i_1241_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v_types_1250_);
lean_del_object(v___x_1246_);
lean_dec(v_i_1241_);
lean_dec(v_ty_1171_);
v___x_1253_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1254_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1253_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_array_fget(v_types_1250_, v_i_1241_);
lean_dec(v_i_1241_);
lean_dec_ref(v_types_1250_);
v___x_1256_ = l_Lean_IR_instBEqIRType_beq(v___x_1255_, v_ty_1171_);
lean_dec(v_ty_1171_);
lean_dec(v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_del_object(v___x_1246_);
v___x_1257_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1258_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1257_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1259_);
v___x_1261_ = v___x_1246_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
case 11:
{
lean_object* v_types_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_types_1263_ = lean_ctor_get(v_a_1244_, 1);
lean_inc_ref(v_types_1263_);
lean_dec_ref_known(v_a_1244_, 2);
v___x_1264_ = lean_array_get_size(v_types_1263_);
v___x_1265_ = lean_nat_dec_lt(v_i_1241_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec_ref(v_types_1263_);
lean_del_object(v___x_1246_);
lean_dec(v_i_1241_);
lean_dec(v_ty_1171_);
v___x_1266_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1267_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1266_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = lean_array_fget(v_types_1263_, v_i_1241_);
lean_dec(v_i_1241_);
lean_dec_ref(v_types_1263_);
v___x_1269_ = l_Lean_IR_instBEqIRType_beq(v___x_1268_, v_ty_1171_);
lean_dec(v_ty_1171_);
lean_dec(v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_del_object(v___x_1246_);
v___x_1270_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1271_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1270_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1272_);
v___x_1274_ = v___x_1246_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
case 12:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
lean_dec(v_i_1241_);
lean_dec(v_ty_1171_);
v___x_1276_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1276_);
v___x_1278_ = v___x_1246_;
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
default: 
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_del_object(v___x_1246_);
lean_dec(v_i_1241_);
lean_dec(v_ty_1171_);
v___x_1280_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1281_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1244_);
v___x_1282_ = l_Std_Format_defWidth;
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = l_Std_Format_pretty(v___x_1281_, v___x_1282_, v___x_1283_, v___x_1283_);
v___x_1285_ = lean_string_append(v___x_1280_, v___x_1284_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1287_ = lean_string_append(v___x_1285_, v___x_1286_);
v___x_1288_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1287_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1288_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_i_1241_);
lean_dec(v_ty_1171_);
v_a_1290_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1243_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1243_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
case 4:
{
lean_object* v_x_1298_; lean_object* v___x_1299_; 
v_x_1298_ = lean_ctor_get(v_e_1172_, 1);
lean_inc(v_x_1298_);
lean_dec_ref_known(v_e_1172_, 2);
v___x_1299_ = l_Lean_IR_Checker_checkObjVar(v_x_1298_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1318_; 
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v___x_1299_, 0);
lean_dec(v_unused_1319_);
v___x_1301_ = v___x_1299_;
v_isShared_1302_ = v_isSharedCheck_1318_;
goto v_resetjp_1300_;
}
else
{
lean_dec(v___x_1299_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1318_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_box(5);
v___x_1304_ = l_Lean_IR_instBEqIRType_beq(v_ty_1171_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_msg_1312_; lean_object* v___x_1313_; 
lean_del_object(v___x_1301_);
v___x_1305_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1306_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1171_);
v___x_1307_ = l_Std_Format_defWidth;
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = l_Std_Format_pretty(v___x_1306_, v___x_1307_, v___x_1308_, v___x_1308_);
v___x_1310_ = lean_string_append(v___x_1305_, v___x_1309_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1312_ = lean_string_append(v___x_1310_, v___x_1311_);
v___x_1313_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1312_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec(v_ty_1171_);
v___x_1314_ = lean_box(0);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1314_);
v___x_1316_ = v___x_1301_;
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
}
else
{
lean_dec(v_ty_1171_);
return v___x_1299_;
}
}
case 5:
{
lean_object* v_x_1320_; lean_object* v___x_1321_; 
v_x_1320_ = lean_ctor_get(v_e_1172_, 2);
lean_inc(v_x_1320_);
lean_dec_ref_known(v_e_1172_, 3);
v___x_1321_ = l_Lean_IR_Checker_checkObjVar(v_x_1320_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1322_; 
lean_dec_ref_known(v___x_1321_, 1);
v___x_1322_ = l_Lean_IR_Checker_checkScalarType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1322_;
}
else
{
lean_dec(v_ty_1171_);
return v___x_1321_;
}
}
case 6:
{
lean_object* v_c_1323_; lean_object* v_ys_1324_; lean_object* v___x_1325_; 
lean_dec(v_ty_1171_);
v_c_1323_ = lean_ctor_get(v_e_1172_, 0);
lean_inc(v_c_1323_);
v_ys_1324_ = lean_ctor_get(v_e_1172_, 1);
lean_inc_ref(v_ys_1324_);
lean_dec_ref_known(v_e_1172_, 2);
v___x_1325_ = l_Lean_IR_Checker_checkFullApp(v_c_1323_, v_ys_1324_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec_ref(v_ys_1324_);
return v___x_1325_;
}
case 7:
{
lean_object* v_c_1326_; lean_object* v_ys_1327_; lean_object* v___x_1328_; 
v_c_1326_ = lean_ctor_get(v_e_1172_, 0);
lean_inc(v_c_1326_);
v_ys_1327_ = lean_ctor_get(v_e_1172_, 1);
lean_inc_ref(v_ys_1327_);
lean_dec_ref_known(v_e_1172_, 2);
v___x_1328_ = l_Lean_IR_Checker_checkPartialApp(v_c_1326_, v_ys_1327_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec_ref(v_ys_1327_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v___x_1329_; 
lean_dec_ref_known(v___x_1328_, 1);
v___x_1329_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1329_;
}
else
{
lean_dec(v_ty_1171_);
return v___x_1328_;
}
}
case 8:
{
lean_object* v_x_1330_; lean_object* v_ys_1331_; lean_object* v___x_1332_; 
v_x_1330_ = lean_ctor_get(v_e_1172_, 0);
lean_inc(v_x_1330_);
v_ys_1331_ = lean_ctor_get(v_e_1172_, 1);
lean_inc_ref(v_ys_1331_);
lean_dec_ref_known(v_e_1172_, 2);
v___x_1332_ = l_Lean_IR_Checker_checkObjVar(v_x_1330_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1333_; 
lean_dec_ref_known(v___x_1332_, 1);
v___x_1333_ = l_Lean_IR_Checker_checkArgs(v_ys_1331_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec_ref(v_ys_1331_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; 
lean_dec_ref_known(v___x_1333_, 1);
v___x_1334_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1334_;
}
else
{
lean_dec(v_ty_1171_);
return v___x_1333_;
}
}
else
{
lean_dec_ref(v_ys_1331_);
lean_dec(v_ty_1171_);
return v___x_1332_;
}
}
case 9:
{
lean_object* v_ty_1335_; lean_object* v_x_1336_; lean_object* v___x_1337_; 
v_ty_1335_ = lean_ctor_get(v_e_1172_, 0);
lean_inc(v_ty_1335_);
v_x_1336_ = lean_ctor_get(v_e_1172_, 1);
lean_inc(v_x_1336_);
lean_dec_ref_known(v_e_1172_, 2);
v___x_1337_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1338_; 
lean_dec_ref_known(v___x_1337_, 1);
lean_inc(v_x_1336_);
v___x_1338_ = l_Lean_IR_Checker_checkScalarVar(v_x_1336_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref_known(v___x_1338_, 1);
v___x_1339_ = l_Lean_IR_Checker_getType(v_x_1336_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1358_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1358_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1358_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_IR_instBEqIRType_beq(v_a_1340_, v_ty_1335_);
lean_dec(v_ty_1335_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_msg_1352_; lean_object* v___x_1353_; 
lean_del_object(v___x_1342_);
v___x_1345_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1346_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1340_);
v___x_1347_ = l_Std_Format_defWidth;
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = l_Std_Format_pretty(v___x_1346_, v___x_1347_, v___x_1348_, v___x_1348_);
v___x_1350_ = lean_string_append(v___x_1345_, v___x_1349_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1352_ = lean_string_append(v___x_1350_, v___x_1351_);
v___x_1353_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1352_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
lean_dec(v_a_1340_);
v___x_1354_ = lean_box(0);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1354_);
v___x_1356_ = v___x_1342_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_ty_1335_);
v_a_1359_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1339_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1339_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_dec(v_x_1336_);
lean_dec(v_ty_1335_);
return v___x_1338_;
}
}
else
{
lean_dec(v_x_1336_);
lean_dec(v_ty_1335_);
return v___x_1337_;
}
}
case 10:
{
lean_object* v_x_1367_; lean_object* v___x_1368_; 
v_x_1367_ = lean_ctor_get(v_e_1172_, 0);
lean_inc(v_x_1367_);
lean_dec_ref_known(v_e_1172_, 1);
v___x_1368_ = l_Lean_IR_Checker_checkScalarType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; 
lean_dec_ref_known(v___x_1368_, 1);
v___x_1369_ = l_Lean_IR_Checker_checkObjVar(v_x_1367_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1369_;
}
else
{
lean_dec(v_x_1367_);
return v___x_1368_;
}
}
case 11:
{
lean_object* v_v_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1379_; 
v_v_1370_ = lean_ctor_get(v_e_1172_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_e_1172_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1372_ = v_e_1172_;
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_v_1370_);
lean_dec(v_e_1172_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
if (lean_obj_tag(v_v_1370_) == 1)
{
lean_object* v___x_1374_; 
lean_dec_ref_known(v_v_1370_, 1);
lean_del_object(v___x_1372_);
v___x_1374_ = l_Lean_IR_Checker_checkObjType(v_ty_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec_ref(v_v_1370_);
lean_dec(v_ty_1171_);
v___x_1375_ = lean_box(0);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1375_);
v___x_1377_ = v___x_1372_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
default: 
{
lean_object* v_x_1380_; lean_object* v___x_1381_; 
v_x_1380_ = lean_ctor_get(v_e_1172_, 0);
lean_inc(v_x_1380_);
lean_dec_ref_known(v_e_1172_, 1);
v___x_1381_ = l_Lean_IR_Checker_checkObjVar(v_x_1380_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1401_);
v___x_1383_ = v___x_1381_;
v_isShared_1384_ = v_isSharedCheck_1400_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v___x_1381_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1400_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = lean_box(1);
v___x_1386_ = l_Lean_IR_instBEqIRType_beq(v_ty_1171_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_msg_1394_; lean_object* v___x_1395_; 
lean_del_object(v___x_1383_);
v___x_1387_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1388_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1171_);
v___x_1389_ = l_Std_Format_defWidth;
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = l_Std_Format_pretty(v___x_1388_, v___x_1389_, v___x_1390_, v___x_1390_);
v___x_1392_ = lean_string_append(v___x_1387_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
v___x_1395_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1394_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1395_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
lean_dec(v_ty_1171_);
v___x_1396_ = lean_box(0);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1396_);
v___x_1398_ = v___x_1383_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_dec(v_ty_1171_);
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1402_, lean_object* v_e_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_IR_Checker_checkExpr(v_ty_1402_, v_e_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1410_, lean_object* v_p_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_x_1417_; lean_object* v___x_1418_; 
v_x_1417_ = lean_ctor_get(v_p_1411_, 0);
lean_inc(v_x_1417_);
v___x_1418_ = l_Lean_IR_Checker_markVar(v_x_1417_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1418_, 0);
lean_dec(v_unused_1427_);
v___x_1420_ = v___x_1418_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_dec(v___x_1418_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = l_Lean_IR_LocalContext_addParam(v_ctx_1410_, v_p_1411_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v_p_1411_);
lean_dec_ref(v_ctx_1410_);
v_a_1428_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1418_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1418_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1436_, lean_object* v_p_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1436_, v_p_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1443_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_instMonadEIO___redArg();
return v___x_1444_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1446_ = l_StateRefT_x27_instMonad___redArg(v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1450_, lean_object* v_k_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v_toApplicative_1458_; lean_object* v_toFunctor_1459_; lean_object* v_toSeq_1460_; lean_object* v_toSeqLeft_1461_; lean_object* v_toSeqRight_1462_; lean_object* v___f_1463_; lean_object* v___f_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v_localCtx_1475_; lean_object* v_currentDecl_1476_; lean_object* v_decls_1477_; lean_object* v_a_1479_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1457_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1458_ = lean_ctor_get(v___x_1457_, 0);
v_toFunctor_1459_ = lean_ctor_get(v_toApplicative_1458_, 0);
v_toSeq_1460_ = lean_ctor_get(v_toApplicative_1458_, 2);
v_toSeqLeft_1461_ = lean_ctor_get(v_toApplicative_1458_, 3);
v_toSeqRight_1462_ = lean_ctor_get(v_toApplicative_1458_, 4);
v___f_1463_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1464_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1459_, 2);
v___f_1465_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1465_, 0, v_toFunctor_1459_);
v___f_1466_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1466_, 0, v_toFunctor_1459_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___f_1465_);
lean_ctor_set(v___x_1467_, 1, v___f_1466_);
lean_inc(v_toSeqRight_1462_);
v___f_1468_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1468_, 0, v_toSeqRight_1462_);
lean_inc(v_toSeqLeft_1461_);
v___f_1469_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1469_, 0, v_toSeqLeft_1461_);
lean_inc(v_toSeq_1460_);
v___f_1470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1470_, 0, v_toSeq_1460_);
v___x_1471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1467_);
lean_ctor_set(v___x_1471_, 1, v___f_1463_);
lean_ctor_set(v___x_1471_, 2, v___f_1470_);
lean_ctor_set(v___x_1471_, 3, v___f_1469_);
lean_ctor_set(v___x_1471_, 4, v___f_1468_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v___f_1464_);
v___x_1473_ = l_StateRefT_x27_instMonad___redArg(v___x_1472_);
v___x_1474_ = l_ReaderT_instMonad___redArg(v___x_1473_);
v_localCtx_1475_ = lean_ctor_get(v_a_1452_, 0);
v_currentDecl_1476_ = lean_ctor_get(v_a_1452_, 1);
v_decls_1477_ = lean_ctor_get(v_a_1452_, 2);
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = lean_array_get_size(v_ps_1450_);
v___x_1484_ = lean_nat_dec_lt(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_dec_ref(v___x_1474_);
lean_dec_ref(v_ps_1450_);
lean_inc_ref(v_localCtx_1475_);
v_a_1479_ = v_localCtx_1475_;
goto v___jp_1478_;
}
else
{
lean_object* v___f_1485_; size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1038__overap_1488_; lean_object* v___x_1489_; 
v___f_1485_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1486_ = ((size_t)0ULL);
v___x_1487_ = lean_usize_of_nat(v___x_1483_);
lean_inc_ref(v_localCtx_1475_);
v___x_1038__overap_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1474_, v___f_1485_, v_ps_1450_, v___x_1486_, v___x_1487_, v_localCtx_1475_);
lean_inc(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
v___x_1489_ = lean_apply_5(v___x_1038__overap_1488_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, lean_box(0));
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v_a_1479_ = v_a_1490_;
goto v___jp_1478_;
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_k_1451_);
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
v___jp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_inc_ref(v_decls_1477_);
lean_inc_ref(v_currentDecl_1476_);
v___x_1480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1480_, 0, v_a_1479_);
lean_ctor_set(v___x_1480_, 1, v_currentDecl_1476_);
lean_ctor_set(v___x_1480_, 2, v_decls_1477_);
lean_inc(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
v___x_1481_ = lean_apply_5(v_k_1451_, v___x_1480_, v_a_1453_, v_a_1454_, v_a_1455_, lean_box(0));
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1499_, lean_object* v_k_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_IR_Checker_withParams(v_ps_1499_, v_k_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1507_, size_t v_i_1508_, size_t v_stop_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_usize_dec_eq(v_i_1508_, v_stop_1509_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v_x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_array_uget_borrowed(v_as_1507_, v_i_1508_);
v_x_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_x_1518_);
v___x_1519_ = l_Lean_IR_Checker_markVar(v_x_1518_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v___x_1520_; size_t v___x_1521_; size_t v___x_1522_; 
lean_dec_ref_known(v___x_1519_, 1);
lean_inc(v___x_1517_);
v___x_1520_ = l_Lean_IR_LocalContext_addParam(v_b_1510_, v___x_1517_);
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_i_1508_, v___x_1521_);
v_i_1508_ = v___x_1522_;
v_b_1510_ = v___x_1520_;
goto _start;
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v_b_1510_);
v_a_1524_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1519_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1519_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_b_1510_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1533_, lean_object* v_i_1534_, lean_object* v_stop_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
size_t v_i_boxed_1542_; size_t v_stop_boxed_1543_; lean_object* v_res_1544_; 
v_i_boxed_1542_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_stop_boxed_1543_ = lean_unbox_usize(v_stop_1535_);
lean_dec(v_stop_1535_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1533_, v_i_boxed_1542_, v_stop_boxed_1543_, v_b_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec_ref(v_as_1533_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_x_1552_; lean_object* v_b_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; 
switch(lean_obj_tag(v_fnBody_1545_))
{
case 0:
{
lean_object* v_x_1560_; lean_object* v_ty_1561_; lean_object* v_e_1562_; lean_object* v_b_1563_; lean_object* v___x_1564_; 
v_x_1560_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_x_1560_);
v_ty_1561_ = lean_ctor_get(v_fnBody_1545_, 1);
lean_inc_n(v_ty_1561_, 2);
v_e_1562_ = lean_ctor_get(v_fnBody_1545_, 2);
lean_inc_ref_n(v_e_1562_, 2);
v_b_1563_ = lean_ctor_get(v_fnBody_1545_, 3);
lean_inc(v_b_1563_);
lean_dec_ref_known(v_fnBody_1545_, 4);
v___x_1564_ = l_Lean_IR_Checker_checkExpr(v_ty_1561_, v_e_1562_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; 
lean_dec_ref_known(v___x_1564_, 1);
lean_inc(v_x_1560_);
v___x_1565_ = l_Lean_IR_Checker_markVar(v_x_1560_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_localCtx_1566_; lean_object* v_currentDecl_1567_; lean_object* v_decls_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec_ref_known(v___x_1565_, 1);
v_localCtx_1566_ = lean_ctor_get(v_a_1546_, 0);
lean_inc_ref(v_localCtx_1566_);
v_currentDecl_1567_ = lean_ctor_get(v_a_1546_, 1);
lean_inc_ref(v_currentDecl_1567_);
v_decls_1568_ = lean_ctor_get(v_a_1546_, 2);
lean_inc_ref(v_decls_1568_);
lean_dec_ref(v_a_1546_);
v___x_1569_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1566_, v_x_1560_, v_ty_1561_, v_e_1562_);
v___x_1570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v_currentDecl_1567_);
lean_ctor_set(v___x_1570_, 2, v_decls_1568_);
v_fnBody_1545_ = v_b_1563_;
v_a_1546_ = v___x_1570_;
goto _start;
}
else
{
lean_dec(v_b_1563_);
lean_dec_ref(v_e_1562_);
lean_dec(v_ty_1561_);
lean_dec(v_x_1560_);
lean_dec_ref(v_a_1546_);
return v___x_1565_;
}
}
else
{
lean_dec(v_b_1563_);
lean_dec_ref(v_e_1562_);
lean_dec(v_ty_1561_);
lean_dec(v_x_1560_);
lean_dec_ref(v_a_1546_);
return v___x_1564_;
}
}
case 1:
{
lean_object* v_j_1572_; lean_object* v_xs_1573_; lean_object* v_v_1574_; lean_object* v_b_1575_; lean_object* v_a_1577_; lean_object* v___x_1586_; 
v_j_1572_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc_n(v_j_1572_, 2);
v_xs_1573_ = lean_ctor_get(v_fnBody_1545_, 1);
lean_inc_ref(v_xs_1573_);
v_v_1574_ = lean_ctor_get(v_fnBody_1545_, 2);
lean_inc(v_v_1574_);
v_b_1575_ = lean_ctor_get(v_fnBody_1545_, 3);
lean_inc(v_b_1575_);
lean_dec_ref_known(v_fnBody_1545_, 4);
v___x_1586_ = l_Lean_IR_Checker_markJP(v_j_1572_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_localCtx_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
lean_dec_ref_known(v___x_1586_, 1);
v_localCtx_1587_ = lean_ctor_get(v_a_1546_, 0);
v___x_1588_ = lean_unsigned_to_nat(0u);
v___x_1589_ = lean_array_get_size(v_xs_1573_);
v___x_1590_ = lean_nat_dec_lt(v___x_1588_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_inc_ref(v_localCtx_1587_);
v_a_1577_ = v_localCtx_1587_;
goto v___jp_1576_;
}
else
{
size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = ((size_t)0ULL);
v___x_1592_ = lean_usize_of_nat(v___x_1589_);
lean_inc_ref(v_localCtx_1587_);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1573_, v___x_1591_, v___x_1592_, v_localCtx_1587_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v_a_1577_ = v_a_1594_;
goto v___jp_1576_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_b_1575_);
lean_dec(v_v_1574_);
lean_dec_ref(v_xs_1573_);
lean_dec(v_j_1572_);
lean_dec_ref(v_a_1546_);
v_a_1595_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1593_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
else
{
lean_dec(v_b_1575_);
lean_dec(v_v_1574_);
lean_dec_ref(v_xs_1573_);
lean_dec(v_j_1572_);
lean_dec_ref(v_a_1546_);
return v___x_1586_;
}
v___jp_1576_:
{
lean_object* v_localCtx_1578_; lean_object* v_currentDecl_1579_; lean_object* v_decls_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_localCtx_1578_ = lean_ctor_get(v_a_1546_, 0);
lean_inc_ref(v_localCtx_1578_);
v_currentDecl_1579_ = lean_ctor_get(v_a_1546_, 1);
lean_inc_ref_n(v_currentDecl_1579_, 2);
v_decls_1580_ = lean_ctor_get(v_a_1546_, 2);
lean_inc_ref_n(v_decls_1580_, 2);
lean_dec_ref(v_a_1546_);
v___x_1581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1581_, 0, v_a_1577_);
lean_ctor_set(v___x_1581_, 1, v_currentDecl_1579_);
lean_ctor_set(v___x_1581_, 2, v_decls_1580_);
lean_inc(v_v_1574_);
v___x_1582_ = l_Lean_IR_Checker_checkFnBody(v_v_1574_, v___x_1581_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec_ref_known(v___x_1582_, 1);
v___x_1583_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1578_, v_j_1572_, v_xs_1573_, v_v_1574_);
v___x_1584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_currentDecl_1579_);
lean_ctor_set(v___x_1584_, 2, v_decls_1580_);
v_fnBody_1545_ = v_b_1575_;
v_a_1546_ = v___x_1584_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1580_);
lean_dec_ref(v_currentDecl_1579_);
lean_dec_ref(v_localCtx_1578_);
lean_dec(v_b_1575_);
lean_dec(v_v_1574_);
lean_dec_ref(v_xs_1573_);
lean_dec(v_j_1572_);
return v___x_1582_;
}
}
}
case 2:
{
lean_object* v_x_1603_; lean_object* v_y_1604_; lean_object* v_b_1605_; lean_object* v___x_1606_; 
v_x_1603_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_x_1603_);
v_y_1604_ = lean_ctor_get(v_fnBody_1545_, 2);
lean_inc(v_y_1604_);
v_b_1605_ = lean_ctor_get(v_fnBody_1545_, 3);
lean_inc(v_b_1605_);
lean_dec_ref_known(v_fnBody_1545_, 4);
v___x_1606_ = l_Lean_IR_Checker_checkVar(v_x_1603_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1607_; 
lean_dec_ref_known(v___x_1606_, 1);
v___x_1607_ = l_Lean_IR_Checker_checkArg(v_y_1604_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_dec_ref_known(v___x_1607_, 1);
v_fnBody_1545_ = v_b_1605_;
goto _start;
}
else
{
lean_dec(v_b_1605_);
lean_dec_ref(v_a_1546_);
return v___x_1607_;
}
}
else
{
lean_dec(v_b_1605_);
lean_dec(v_y_1604_);
lean_dec_ref(v_a_1546_);
return v___x_1606_;
}
}
case 3:
{
lean_object* v_x_1609_; lean_object* v_b_1610_; lean_object* v___x_1611_; 
v_x_1609_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_x_1609_);
v_b_1610_ = lean_ctor_get(v_fnBody_1545_, 2);
lean_inc(v_b_1610_);
lean_dec_ref_known(v_fnBody_1545_, 3);
v___x_1611_ = l_Lean_IR_Checker_checkVar(v_x_1609_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_dec_ref_known(v___x_1611_, 1);
v_fnBody_1545_ = v_b_1610_;
goto _start;
}
else
{
lean_dec(v_b_1610_);
lean_dec_ref(v_a_1546_);
return v___x_1611_;
}
}
case 4:
{
lean_object* v_x_1613_; lean_object* v_y_1614_; lean_object* v_b_1615_; lean_object* v___x_1616_; 
v_x_1613_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_x_1613_);
v_y_1614_ = lean_ctor_get(v_fnBody_1545_, 2);
lean_inc(v_y_1614_);
v_b_1615_ = lean_ctor_get(v_fnBody_1545_, 3);
lean_inc(v_b_1615_);
lean_dec_ref_known(v_fnBody_1545_, 4);
v___x_1616_ = l_Lean_IR_Checker_checkVar(v_x_1613_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1617_; 
lean_dec_ref_known(v___x_1616_, 1);
v___x_1617_ = l_Lean_IR_Checker_checkVar(v_y_1614_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_dec_ref_known(v___x_1617_, 1);
v_fnBody_1545_ = v_b_1615_;
goto _start;
}
else
{
lean_dec(v_b_1615_);
lean_dec_ref(v_a_1546_);
return v___x_1617_;
}
}
else
{
lean_dec(v_b_1615_);
lean_dec(v_y_1614_);
lean_dec_ref(v_a_1546_);
return v___x_1616_;
}
}
case 5:
{
lean_object* v_x_1619_; lean_object* v_y_1620_; lean_object* v_b_1621_; lean_object* v___x_1622_; 
v_x_1619_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_x_1619_);
v_y_1620_ = lean_ctor_get(v_fnBody_1545_, 3);
lean_inc(v_y_1620_);
v_b_1621_ = lean_ctor_get(v_fnBody_1545_, 5);
lean_inc(v_b_1621_);
lean_dec_ref_known(v_fnBody_1545_, 6);
v___x_1622_ = l_Lean_IR_Checker_checkVar(v_x_1619_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1623_; 
lean_dec_ref_known(v___x_1622_, 1);
v___x_1623_ = l_Lean_IR_Checker_checkVar(v_y_1620_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_dec_ref_known(v___x_1623_, 1);
v_fnBody_1545_ = v_b_1621_;
goto _start;
}
else
{
lean_dec(v_b_1621_);
lean_dec_ref(v_a_1546_);
return v___x_1623_;
}
}
else
{
lean_dec(v_b_1621_);
lean_dec(v_y_1620_);
lean_dec_ref(v_a_1546_);
return v___x_1622_;
}
}
case 8:
{
lean_object* v_x_1625_; lean_object* v_b_1626_; lean_object* v___x_1627_; 
v_x_1625_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_x_1625_);
v_b_1626_ = lean_ctor_get(v_fnBody_1545_, 1);
lean_inc(v_b_1626_);
lean_dec_ref_known(v_fnBody_1545_, 2);
v___x_1627_ = l_Lean_IR_Checker_checkVar(v_x_1625_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref_known(v___x_1627_, 1);
v_fnBody_1545_ = v_b_1626_;
goto _start;
}
else
{
lean_dec(v_b_1626_);
lean_dec_ref(v_a_1546_);
return v___x_1627_;
}
}
case 9:
{
lean_object* v_x_1629_; lean_object* v_cs_1630_; lean_object* v___x_1631_; 
v_x_1629_ = lean_ctor_get(v_fnBody_1545_, 1);
lean_inc(v_x_1629_);
v_cs_1630_ = lean_ctor_get(v_fnBody_1545_, 3);
lean_inc_ref(v_cs_1630_);
lean_dec_ref_known(v_fnBody_1545_, 4);
v___x_1631_ = l_Lean_IR_Checker_checkVar(v_x_1629_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1645_; 
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1631_, 0);
lean_dec(v_unused_1646_);
v___x_1633_ = v___x_1631_;
v_isShared_1634_ = v_isSharedCheck_1645_;
goto v_resetjp_1632_;
}
else
{
lean_dec(v___x_1631_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1645_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = lean_array_get_size(v_cs_1630_);
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_nat_dec_lt(v___x_1635_, v___x_1636_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1640_; 
lean_dec_ref(v_cs_1630_);
lean_dec_ref(v_a_1546_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1637_);
v___x_1640_ = v___x_1633_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1637_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
else
{
size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1633_);
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = lean_usize_of_nat(v___x_1636_);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1630_, v___x_1642_, v___x_1643_, v___x_1637_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec_ref(v_a_1546_);
lean_dec_ref(v_cs_1630_);
return v___x_1644_;
}
}
}
else
{
lean_dec_ref(v_cs_1630_);
lean_dec_ref(v_a_1546_);
return v___x_1631_;
}
}
case 10:
{
lean_object* v_x_1647_; lean_object* v___x_1648_; 
v_x_1647_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_x_1647_);
lean_dec_ref_known(v_fnBody_1545_, 1);
v___x_1648_ = l_Lean_IR_Checker_checkArg(v_x_1647_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec_ref(v_a_1546_);
return v___x_1648_;
}
case 11:
{
lean_object* v_j_1649_; lean_object* v_ys_1650_; lean_object* v___x_1651_; 
v_j_1649_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_j_1649_);
v_ys_1650_ = lean_ctor_get(v_fnBody_1545_, 1);
lean_inc_ref(v_ys_1650_);
lean_dec_ref_known(v_fnBody_1545_, 2);
v___x_1651_ = l_Lean_IR_Checker_checkJP(v_j_1649_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v___x_1652_; 
lean_dec_ref_known(v___x_1651_, 1);
v___x_1652_ = l_Lean_IR_Checker_checkArgs(v_ys_1650_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec_ref(v_a_1546_);
lean_dec_ref(v_ys_1650_);
return v___x_1652_;
}
else
{
lean_dec_ref(v_ys_1650_);
lean_dec_ref(v_a_1546_);
return v___x_1651_;
}
}
case 12:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v_a_1546_);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
default: 
{
lean_object* v_x_1655_; lean_object* v_b_1656_; 
v_x_1655_ = lean_ctor_get(v_fnBody_1545_, 0);
lean_inc(v_x_1655_);
v_b_1656_ = lean_ctor_get(v_fnBody_1545_, 2);
lean_inc(v_b_1656_);
lean_dec(v_fnBody_1545_);
v_x_1552_ = v_x_1655_;
v_b_1553_ = v_b_1656_;
v___y_1554_ = v_a_1546_;
v___y_1555_ = v_a_1547_;
v___y_1556_ = v_a_1548_;
v___y_1557_ = v_a_1549_;
goto v___jp_1551_;
}
}
v___jp_1551_:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_IR_Checker_checkVar(v_x_1552_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_dec_ref_known(v___x_1558_, 1);
v_fnBody_1545_ = v_b_1553_;
v_a_1546_ = v___y_1554_;
v_a_1547_ = v___y_1555_;
v_a_1548_ = v___y_1556_;
v_a_1549_ = v___y_1557_;
goto _start;
}
else
{
lean_dec_ref(v___y_1554_);
lean_dec(v_b_1553_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1657_, size_t v_i_1658_, size_t v_stop_1659_, lean_object* v_b_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_eq(v_i_1658_, v_stop_1659_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = lean_array_uget_borrowed(v_as_1657_, v_i_1658_);
v___x_1668_ = l_Lean_IR_Alt_body(v___x_1667_);
lean_inc_ref(v___y_1661_);
v___x_1669_ = l_Lean_IR_Checker_checkFnBody(v___x_1668_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; size_t v___x_1671_; size_t v___x_1672_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_add(v_i_1658_, v___x_1671_);
v_i_1658_ = v___x_1672_;
v_b_1660_ = v_a_1670_;
goto _start;
}
else
{
return v___x_1669_;
}
}
else
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_b_1660_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1675_, lean_object* v_i_1676_, lean_object* v_stop_1677_, lean_object* v_b_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
size_t v_i_boxed_1684_; size_t v_stop_boxed_1685_; lean_object* v_res_1686_; 
v_i_boxed_1684_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_stop_boxed_1685_ = lean_unbox_usize(v_stop_1677_);
lean_dec(v_stop_1677_);
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1675_, v_i_boxed_1684_, v_stop_boxed_1685_, v_b_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec_ref(v_as_1675_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
if (lean_obj_tag(v_x_1694_) == 0)
{
lean_object* v_xs_1700_; lean_object* v_body_1701_; lean_object* v_localCtx_1702_; lean_object* v_currentDecl_1703_; lean_object* v_decls_1704_; lean_object* v_a_1706_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_xs_1700_ = lean_ctor_get(v_x_1694_, 1);
lean_inc_ref(v_xs_1700_);
v_body_1701_ = lean_ctor_get(v_x_1694_, 3);
lean_inc(v_body_1701_);
lean_dec_ref_known(v_x_1694_, 5);
v_localCtx_1702_ = lean_ctor_get(v_a_1695_, 0);
v_currentDecl_1703_ = lean_ctor_get(v_a_1695_, 1);
v_decls_1704_ = lean_ctor_get(v_a_1695_, 2);
v___x_1709_ = lean_unsigned_to_nat(0u);
v___x_1710_ = lean_array_get_size(v_xs_1700_);
v___x_1711_ = lean_nat_dec_lt(v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_dec_ref(v_xs_1700_);
lean_inc_ref(v_localCtx_1702_);
v_a_1706_ = v_localCtx_1702_;
goto v___jp_1705_;
}
else
{
size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = lean_usize_of_nat(v___x_1710_);
lean_inc_ref(v_localCtx_1702_);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1700_, v___x_1712_, v___x_1713_, v_localCtx_1702_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec_ref(v_xs_1700_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v_a_1706_ = v_a_1715_;
goto v___jp_1705_;
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_body_1701_);
v_a_1716_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1714_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1714_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
v___jp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_inc_ref(v_decls_1704_);
lean_inc_ref(v_currentDecl_1703_);
v___x_1707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1707_, 0, v_a_1706_);
lean_ctor_set(v___x_1707_, 1, v_currentDecl_1703_);
lean_ctor_set(v___x_1707_, 2, v_decls_1704_);
v___x_1708_ = l_Lean_IR_Checker_checkFnBody(v_body_1701_, v___x_1707_, v_a_1696_, v_a_1697_, v_a_1698_);
return v___x_1708_;
}
}
else
{
lean_object* v_xs_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_xs_1724_ = lean_ctor_get(v_x_1694_, 1);
lean_inc_ref(v_xs_1724_);
lean_dec_ref_known(v_x_1694_, 4);
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_array_get_size(v_xs_1724_);
v___x_1728_ = lean_nat_dec_lt(v___x_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref(v_xs_1724_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1725_);
return v___x_1729_;
}
else
{
lean_object* v_localCtx_1730_; size_t v___x_1731_; size_t v___x_1732_; lean_object* v___x_1733_; 
v_localCtx_1730_ = lean_ctor_get(v_a_1695_, 0);
v___x_1731_ = ((size_t)0ULL);
v___x_1732_ = lean_usize_of_nat(v___x_1727_);
lean_inc_ref(v_localCtx_1730_);
v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1724_, v___x_1731_, v___x_1732_, v_localCtx_1730_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec_ref(v_xs_1724_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1740_ == 0)
{
lean_object* v_unused_1741_; 
v_unused_1741_ = lean_ctor_get(v___x_1733_, 0);
lean_dec(v_unused_1741_);
v___x_1735_ = v___x_1733_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v___x_1733_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1725_);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1725_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_a_1742_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1733_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1733_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_IR_Checker_checkDecl(v_x_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_){
_start:
{
lean_object* v_ks_1761_; lean_object* v_vs_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1786_; 
v_ks_1761_ = lean_ctor_get(v_x_1757_, 0);
v_vs_1762_ = lean_ctor_get(v_x_1757_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_x_1757_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1764_ = v_x_1757_;
v_isShared_1765_ = v_isSharedCheck_1786_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_vs_1762_);
lean_inc(v_ks_1761_);
lean_dec(v_x_1757_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1786_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_array_get_size(v_ks_1761_);
v___x_1767_ = lean_nat_dec_lt(v_x_1758_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_dec(v_x_1758_);
v___x_1768_ = lean_array_push(v_ks_1761_, v_x_1759_);
v___x_1769_ = lean_array_push(v_vs_1762_, v_x_1760_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1769_);
lean_ctor_set(v___x_1764_, 0, v___x_1768_);
v___x_1771_ = v___x_1764_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
lean_object* v_k_x27_1773_; uint8_t v___x_1774_; 
v_k_x27_1773_ = lean_array_fget_borrowed(v_ks_1761_, v_x_1758_);
v___x_1774_ = lean_name_eq(v_x_1759_, v_k_x27_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1776_; 
if (v_isShared_1765_ == 0)
{
v___x_1776_ = v___x_1764_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_ks_1761_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_vs_1762_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v_x_1758_, v___x_1777_);
lean_dec(v_x_1758_);
v_x_1757_ = v___x_1776_;
v_x_1758_ = v___x_1778_;
goto _start;
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1781_ = lean_array_fset(v_ks_1761_, v_x_1758_, v_x_1759_);
v___x_1782_ = lean_array_fset(v_vs_1762_, v_x_1758_, v_x_1760_);
lean_dec(v_x_1758_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1782_);
lean_ctor_set(v___x_1764_, 0, v___x_1781_);
v___x_1784_ = v___x_1764_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1787_, lean_object* v_k_1788_, lean_object* v_v_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1787_, v___x_1790_, v_k_1788_, v_v_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(lean_object* v_x_1793_, size_t v_x_1794_, size_t v_x_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
lean_object* v_es_1798_; size_t v___x_1799_; size_t v___x_1800_; lean_object* v_j_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_es_1798_ = lean_ctor_get(v_x_1793_, 0);
v___x_1799_ = ((size_t)31ULL);
v___x_1800_ = lean_usize_land(v_x_1794_, v___x_1799_);
v_j_1801_ = lean_usize_to_nat(v___x_1800_);
v___x_1802_ = lean_array_get_size(v_es_1798_);
v___x_1803_ = lean_nat_dec_lt(v_j_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec(v_j_1801_);
lean_dec(v_x_1797_);
lean_dec(v_x_1796_);
return v_x_1793_;
}
else
{
lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1842_; 
lean_inc_ref(v_es_1798_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_x_1793_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v_x_1793_, 0);
lean_dec(v_unused_1843_);
v___x_1805_ = v_x_1793_;
v_isShared_1806_ = v_isSharedCheck_1842_;
goto v_resetjp_1804_;
}
else
{
lean_dec(v_x_1793_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1842_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_v_1807_; lean_object* v___x_1808_; lean_object* v_xs_x27_1809_; lean_object* v___y_1811_; 
v_v_1807_ = lean_array_fget(v_es_1798_, v_j_1801_);
v___x_1808_ = lean_box(0);
v_xs_x27_1809_ = lean_array_fset(v_es_1798_, v_j_1801_, v___x_1808_);
switch(lean_obj_tag(v_v_1807_))
{
case 0:
{
lean_object* v_key_1816_; lean_object* v_val_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1827_; 
v_key_1816_ = lean_ctor_get(v_v_1807_, 0);
v_val_1817_ = lean_ctor_get(v_v_1807_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_v_1807_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1819_ = v_v_1807_;
v_isShared_1820_ = v_isSharedCheck_1827_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_val_1817_);
lean_inc(v_key_1816_);
lean_dec(v_v_1807_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1827_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_name_eq(v_x_1796_, v_key_1816_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_del_object(v___x_1819_);
v___x_1822_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1816_, v_val_1817_, v_x_1796_, v_x_1797_);
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
v___y_1811_ = v___x_1823_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1825_; 
lean_dec(v_val_1817_);
lean_dec(v_key_1816_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v_x_1797_);
lean_ctor_set(v___x_1819_, 0, v_x_1796_);
v___x_1825_ = v___x_1819_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_x_1796_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_x_1797_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
v___y_1811_ = v___x_1825_;
goto v___jp_1810_;
}
}
}
}
case 1:
{
lean_object* v_node_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1840_; 
v_node_1828_ = lean_ctor_get(v_v_1807_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_v_1807_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1830_ = v_v_1807_;
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_node_1828_);
lean_dec(v_v_1807_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
size_t v___x_1832_; size_t v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1832_ = ((size_t)5ULL);
v___x_1833_ = lean_usize_shift_right(v_x_1794_, v___x_1832_);
v___x_1834_ = ((size_t)1ULL);
v___x_1835_ = lean_usize_add(v_x_1795_, v___x_1834_);
v___x_1836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_node_1828_, v___x_1833_, v___x_1835_, v_x_1796_, v_x_1797_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1836_);
v___x_1838_ = v___x_1830_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
v___y_1811_ = v___x_1838_;
goto v___jp_1810_;
}
}
}
default: 
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_x_1796_);
lean_ctor_set(v___x_1841_, 1, v_x_1797_);
v___y_1811_ = v___x_1841_;
goto v___jp_1810_;
}
}
v___jp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_array_fset(v_xs_x27_1809_, v_j_1801_, v___y_1811_);
lean_dec(v_j_1801_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1812_);
v___x_1814_ = v___x_1805_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_object* v_ks_1844_; lean_object* v_vs_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1863_; 
v_ks_1844_ = lean_ctor_get(v_x_1793_, 0);
v_vs_1845_ = lean_ctor_get(v_x_1793_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_x_1793_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1847_ = v_x_1793_;
v_isShared_1848_ = v_isSharedCheck_1863_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_vs_1845_);
lean_inc(v_ks_1844_);
lean_dec(v_x_1793_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1863_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_ks_1844_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_vs_1845_);
v___x_1850_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v_newNode_1851_; size_t v___x_1852_; uint8_t v___x_1853_; 
v_newNode_1851_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1___redArg(v___x_1850_, v_x_1796_, v_x_1797_);
v___x_1852_ = ((size_t)7ULL);
v___x_1853_ = lean_usize_dec_le(v___x_1852_, v_x_1795_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1851_);
v___x_1855_ = lean_unsigned_to_nat(4u);
v___x_1856_ = lean_nat_dec_lt(v___x_1854_, v___x_1855_);
lean_dec(v___x_1854_);
if (v___x_1856_ == 0)
{
lean_object* v_ks_1857_; lean_object* v_vs_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_ks_1857_ = lean_ctor_get(v_newNode_1851_, 0);
lean_inc_ref(v_ks_1857_);
v_vs_1858_ = lean_ctor_get(v_newNode_1851_, 1);
lean_inc_ref(v_vs_1858_);
lean_dec_ref(v_newNode_1851_);
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0);
v___x_1861_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(v_x_1795_, v_ks_1857_, v_vs_1858_, v___x_1859_, v___x_1860_);
lean_dec_ref(v_vs_1858_);
lean_dec_ref(v_ks_1857_);
return v___x_1861_;
}
else
{
return v_newNode_1851_;
}
}
else
{
return v_newNode_1851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(size_t v_depth_1864_, lean_object* v_keys_1865_, lean_object* v_vals_1866_, lean_object* v_i_1867_, lean_object* v_entries_1868_){
_start:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = lean_array_get_size(v_keys_1865_);
v___x_1870_ = lean_nat_dec_lt(v_i_1867_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_dec(v_i_1867_);
return v_entries_1868_;
}
else
{
lean_object* v_k_1871_; lean_object* v_v_1872_; uint64_t v___y_1874_; 
v_k_1871_ = lean_array_fget_borrowed(v_keys_1865_, v_i_1867_);
v_v_1872_ = lean_array_fget_borrowed(v_vals_1866_, v_i_1867_);
if (lean_obj_tag(v_k_1871_) == 0)
{
uint64_t v___x_1885_; 
v___x_1885_ = 1723ULL;
v___y_1874_ = v___x_1885_;
goto v___jp_1873_;
}
else
{
uint64_t v_hash_1886_; 
v_hash_1886_ = lean_ctor_get_uint64(v_k_1871_, sizeof(void*)*2);
v___y_1874_ = v_hash_1886_;
goto v___jp_1873_;
}
v___jp_1873_:
{
size_t v_h_1875_; size_t v___x_1876_; lean_object* v___x_1877_; size_t v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; size_t v_h_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_h_1875_ = lean_uint64_to_usize(v___y_1874_);
v___x_1876_ = ((size_t)5ULL);
v___x_1877_ = lean_unsigned_to_nat(1u);
v___x_1878_ = ((size_t)1ULL);
v___x_1879_ = lean_usize_sub(v_depth_1864_, v___x_1878_);
v___x_1880_ = lean_usize_mul(v___x_1876_, v___x_1879_);
v_h_1881_ = lean_usize_shift_right(v_h_1875_, v___x_1880_);
v___x_1882_ = lean_nat_add(v_i_1867_, v___x_1877_);
lean_dec(v_i_1867_);
lean_inc(v_v_1872_);
lean_inc(v_k_1871_);
v___x_1883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_entries_1868_, v_h_1881_, v_depth_1864_, v_k_1871_, v_v_1872_);
v_i_1867_ = v___x_1882_;
v_entries_1868_ = v___x_1883_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1887_, lean_object* v_keys_1888_, lean_object* v_vals_1889_, lean_object* v_i_1890_, lean_object* v_entries_1891_){
_start:
{
size_t v_depth_boxed_1892_; lean_object* v_res_1893_; 
v_depth_boxed_1892_ = lean_unbox_usize(v_depth_1887_);
lean_dec(v_depth_1887_);
v_res_1893_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1892_, v_keys_1888_, v_vals_1889_, v_i_1890_, v_entries_1891_);
lean_dec_ref(v_vals_1889_);
lean_dec_ref(v_keys_1888_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___boxed(lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
size_t v_x_516__boxed_1899_; size_t v_x_517__boxed_1900_; lean_object* v_res_1901_; 
v_x_516__boxed_1899_ = lean_unbox_usize(v_x_1895_);
lean_dec(v_x_1895_);
v_x_517__boxed_1900_ = lean_unbox_usize(v_x_1896_);
lean_dec(v_x_1896_);
v_res_1901_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_x_1894_, v_x_516__boxed_1899_, v_x_517__boxed_1900_, v_x_1897_, v_x_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0___redArg(lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_){
_start:
{
uint64_t v___y_1906_; 
if (lean_obj_tag(v_x_1903_) == 0)
{
uint64_t v___x_1910_; 
v___x_1910_ = 1723ULL;
v___y_1906_ = v___x_1910_;
goto v___jp_1905_;
}
else
{
uint64_t v_hash_1911_; 
v_hash_1911_ = lean_ctor_get_uint64(v_x_1903_, sizeof(void*)*2);
v___y_1906_ = v_hash_1911_;
goto v___jp_1905_;
}
v___jp_1905_:
{
size_t v___x_1907_; size_t v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_uint64_to_usize(v___y_1906_);
v___x_1908_ = ((size_t)1ULL);
v___x_1909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_x_1902_, v___x_1907_, v___x_1908_, v_x_1903_, v_x_1904_);
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1(lean_object* v_as_1912_, size_t v_i_1913_, size_t v_stop_1914_, lean_object* v_b_1915_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_usize_dec_eq(v_i_1913_, v_stop_1914_);
if (v___x_1916_ == 0)
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1917_ = ((size_t)1ULL);
v___x_1918_ = lean_usize_sub(v_i_1913_, v___x_1917_);
v___x_1919_ = lean_array_uget_borrowed(v_as_1912_, v___x_1918_);
v___x_1920_ = l_Lean_IR_Decl_name(v___x_1919_);
lean_inc(v___x_1919_);
v___x_1921_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0___redArg(v_b_1915_, v___x_1920_, v___x_1919_);
v_i_1913_ = v___x_1918_;
v_b_1915_ = v___x_1921_;
goto _start;
}
else
{
return v_b_1915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1___boxed(lean_object* v_as_1923_, lean_object* v_i_1924_, lean_object* v_stop_1925_, lean_object* v_b_1926_){
_start:
{
size_t v_i_boxed_1927_; size_t v_stop_boxed_1928_; lean_object* v_res_1929_; 
v_i_boxed_1927_ = lean_unbox_usize(v_i_1924_);
lean_dec(v_i_1924_);
v_stop_boxed_1928_ = lean_unbox_usize(v_stop_1925_);
lean_dec(v_stop_1925_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1(v_as_1923_, v_i_boxed_1927_, v_stop_boxed_1928_, v_b_1926_);
lean_dec_ref(v_as_1923_);
return v_res_1929_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(lean_object* v_decls_1932_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1933_ = lean_obj_once(&l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0, &l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0_once, _init_l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0);
v___x_1934_ = lean_array_get_size(v_decls_1932_);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_nat_dec_lt(v___x_1935_, v___x_1934_);
if (v___x_1936_ == 0)
{
return v___x_1933_;
}
else
{
size_t v___x_1937_; size_t v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = lean_usize_of_nat(v___x_1934_);
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1(v_decls_1932_, v___x_1937_, v___x_1938_, v___x_1933_);
return v___x_1939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___boxed(lean_object* v_decls_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(v_decls_1940_);
lean_dec_ref(v_decls_1940_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0(lean_object* v_00_u03b2_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0___redArg(v_x_1943_, v_x_1944_, v_x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0(lean_object* v_00_u03b2_1947_, lean_object* v_x_1948_, size_t v_x_1949_, size_t v_x_1950_, lean_object* v_x_1951_, lean_object* v_x_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_x_1948_, v_x_1949_, v_x_1950_, v_x_1951_, v_x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_){
_start:
{
size_t v_x_731__boxed_1960_; size_t v_x_732__boxed_1961_; lean_object* v_res_1962_; 
v_x_731__boxed_1960_ = lean_unbox_usize(v_x_1956_);
lean_dec(v_x_1956_);
v_x_732__boxed_1961_ = lean_unbox_usize(v_x_1957_);
lean_dec(v_x_1957_);
v_res_1962_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0(v_00_u03b2_1954_, v_x_1955_, v_x_731__boxed_1960_, v_x_732__boxed_1961_, v_x_1958_, v_x_1959_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1963_, lean_object* v_n_1964_, lean_object* v_k_1965_, lean_object* v_v_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1___redArg(v_n_1964_, v_k_1965_, v_v_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1968_, size_t v_depth_1969_, lean_object* v_keys_1970_, lean_object* v_vals_1971_, lean_object* v_heq_1972_, lean_object* v_i_1973_, lean_object* v_entries_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(v_depth_1969_, v_keys_1970_, v_vals_1971_, v_i_1973_, v_entries_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1976_, lean_object* v_depth_1977_, lean_object* v_keys_1978_, lean_object* v_vals_1979_, lean_object* v_heq_1980_, lean_object* v_i_1981_, lean_object* v_entries_1982_){
_start:
{
size_t v_depth_boxed_1983_; lean_object* v_res_1984_; 
v_depth_boxed_1983_ = lean_unbox_usize(v_depth_1977_);
lean_dec(v_depth_1977_);
v_res_1984_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2(v_00_u03b2_1976_, v_depth_boxed_1983_, v_keys_1978_, v_vals_1979_, v_heq_1980_, v_i_1981_, v_entries_1982_);
lean_dec_ref(v_vals_1979_);
lean_dec_ref(v_keys_1978_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1986_, v_x_1987_, v_x_1988_, v_x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(lean_object* v_decls_1995_, lean_object* v_decl_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__0));
lean_inc_ref(v_decl_1996_);
v___x_2001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v_decl_1996_);
lean_ctor_set(v___x_2001_, 2, v_decls_1995_);
v___x_2002_ = ((lean_object*)(l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__1));
v___x_2003_ = lean_st_mk_ref(v___x_2002_);
v___x_2004_ = l_Lean_IR_Checker_checkDecl(v_decl_1996_, v___x_2001_, v___x_2003_, v_a_1997_, v_a_1998_);
lean_dec_ref_known(v___x_2001_, 3);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2013_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2013_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2013_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2009_ = lean_st_ref_get(v___x_2003_);
lean_dec(v___x_2003_);
lean_dec(v___x_2009_);
if (v_isShared_2008_ == 0)
{
v___x_2011_ = v___x_2007_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2005_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
else
{
lean_dec(v___x_2003_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___boxed(lean_object* v_decls_2014_, lean_object* v_decl_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(v_decls_2014_, v_decl_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_2020_, lean_object* v_decl_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(v_decls_2020_);
v___x_2026_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(v___x_2025_, v_decl_2021_, v_a_2022_, v_a_2023_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* v_decls_2027_, lean_object* v_decl_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_IR_checkDecl(v_decls_2027_, v_decl_2028_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec_ref(v_decls_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* v_declMap_2033_, lean_object* v_as_2034_, size_t v_i_2035_, size_t v_stop_2036_, lean_object* v_b_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
uint8_t v___x_2041_; 
v___x_2041_ = lean_usize_dec_eq(v_i_2035_, v_stop_2036_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_array_uget_borrowed(v_as_2034_, v_i_2035_);
lean_inc(v___x_2042_);
lean_inc_ref(v_declMap_2033_);
v___x_2043_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(v_declMap_2033_, v___x_2042_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; size_t v___x_2045_; size_t v___x_2046_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_add(v_i_2035_, v___x_2045_);
v_i_2035_ = v___x_2046_;
v_b_2037_ = v_a_2044_;
goto _start;
}
else
{
lean_dec_ref(v_declMap_2033_);
return v___x_2043_;
}
}
else
{
lean_object* v___x_2048_; 
lean_dec_ref(v_declMap_2033_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_b_2037_);
return v___x_2048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* v_declMap_2049_, lean_object* v_as_2050_, lean_object* v_i_2051_, lean_object* v_stop_2052_, lean_object* v_b_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
size_t v_i_boxed_2057_; size_t v_stop_boxed_2058_; lean_object* v_res_2059_; 
v_i_boxed_2057_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_stop_boxed_2058_ = lean_unbox_usize(v_stop_2052_);
lean_dec(v_stop_2052_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_declMap_2049_, v_as_2050_, v_i_boxed_2057_, v_stop_boxed_2058_, v_b_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec_ref(v_as_2050_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* v_decls_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = lean_array_get_size(v_decls_2060_);
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_nat_dec_lt(v___x_2064_, v___x_2065_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2066_);
return v___x_2068_;
}
else
{
lean_object* v_declMap_2069_; size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v_declMap_2069_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(v_decls_2060_);
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = lean_usize_of_nat(v___x_2065_);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_declMap_2069_, v_decls_2060_, v___x_2070_, v___x_2071_, v___x_2066_, v_a_2061_, v_a_2062_);
return v___x_2072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_IR_checkDecls(v_decls_2073_, v_a_2074_, v_a_2075_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec_ref(v_decls_2073_);
return v_res_2077_;
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
