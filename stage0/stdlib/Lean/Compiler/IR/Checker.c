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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
v___x_187_ = lean_nat_add(v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec(v___y_185_);
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
lean_ctor_set(v___x_167_, 3, v___y_184_);
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
lean_ctor_set(v_reuseFailAlloc_192_, 3, v___y_184_);
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
v___y_184_ = v___x_198_;
v___y_185_ = v___x_199_;
v___y_186_ = v_size_200_;
goto v___jp_183_;
}
else
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___y_184_ = v___x_198_;
v___y_185_ = v___x_199_;
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
v___x_325_ = lean_nat_add(v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec(v___y_323_);
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
lean_ctor_set(v___x_305_, 3, v___y_322_);
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
lean_ctor_set(v_reuseFailAlloc_330_, 3, v___y_322_);
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
v___y_322_ = v___x_337_;
v___y_323_ = v___x_338_;
v___y_324_ = v_size_339_;
goto v___jp_321_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_unsigned_to_nat(0u);
v___y_322_ = v___x_337_;
v___y_323_ = v___x_338_;
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
v___x_496_ = lean_st_ref_put(v___y_492_, v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___y_491_);
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
v___y_491_ = v___x_503_;
v___y_492_ = v___y_499_;
v___y_493_ = v_foundVars_501_;
v___y_494_ = v___x_505_;
goto v___jp_490_;
}
else
{
lean_dec(v_j_484_);
v___y_491_ = v___x_503_;
v___y_492_ = v___y_499_;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_522_, lean_object* v_vals_523_, lean_object* v_i_524_, lean_object* v_k_525_){
_start:
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_array_get_size(v_keys_522_);
v___x_527_ = lean_nat_dec_lt(v_i_524_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v_i_524_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v_k_x27_529_; uint8_t v___x_530_; 
v_k_x27_529_ = lean_array_fget_borrowed(v_keys_522_, v_i_524_);
v___x_530_ = lean_name_eq(v_k_525_, v_k_x27_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_i_524_, v___x_531_);
lean_dec(v_i_524_);
v_i_524_ = v___x_532_;
goto _start;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_array_fget_borrowed(v_vals_523_, v_i_524_);
lean_dec(v_i_524_);
lean_inc(v___x_534_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_536_, lean_object* v_vals_537_, lean_object* v_i_538_, lean_object* v_k_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(v_keys_536_, v_vals_537_, v_i_538_, v_k_539_);
lean_dec(v_k_539_);
lean_dec_ref(v_vals_537_);
lean_dec_ref(v_keys_536_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(lean_object* v_x_541_, size_t v_x_542_, lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v_es_544_; lean_object* v___x_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v_j_548_; lean_object* v___x_549_; 
v_es_544_ = lean_ctor_get(v_x_541_, 0);
v___x_545_ = lean_box(2);
v___x_546_ = ((size_t)31ULL);
v___x_547_ = lean_usize_land(v_x_542_, v___x_546_);
v_j_548_ = lean_usize_to_nat(v___x_547_);
v___x_549_ = lean_array_get_borrowed(v___x_545_, v_es_544_, v_j_548_);
lean_dec(v_j_548_);
switch(lean_obj_tag(v___x_549_))
{
case 0:
{
lean_object* v_key_550_; lean_object* v_val_551_; uint8_t v___x_552_; 
v_key_550_ = lean_ctor_get(v___x_549_, 0);
v_val_551_ = lean_ctor_get(v___x_549_, 1);
v___x_552_ = lean_name_eq(v_x_543_, v_key_550_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
v___x_553_ = lean_box(0);
return v___x_553_;
}
else
{
lean_object* v___x_554_; 
lean_inc(v_val_551_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_val_551_);
return v___x_554_;
}
}
case 1:
{
lean_object* v_node_555_; size_t v___x_556_; size_t v___x_557_; 
v_node_555_ = lean_ctor_get(v___x_549_, 0);
v___x_556_ = ((size_t)5ULL);
v___x_557_ = lean_usize_shift_right(v_x_542_, v___x_556_);
v_x_541_ = v_node_555_;
v_x_542_ = v___x_557_;
goto _start;
}
default: 
{
lean_object* v___x_559_; 
v___x_559_ = lean_box(0);
return v___x_559_;
}
}
}
else
{
lean_object* v_ks_560_; lean_object* v_vs_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_ks_560_ = lean_ctor_get(v_x_541_, 0);
v_vs_561_ = lean_ctor_get(v_x_541_, 1);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(v_ks_560_, v_vs_561_, v___x_562_, v_x_543_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
size_t v_x_1166__boxed_567_; lean_object* v_res_568_; 
v_x_1166__boxed_567_ = lean_unbox_usize(v_x_565_);
lean_dec(v_x_565_);
v_res_568_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(v_x_564_, v_x_1166__boxed_567_, v_x_566_);
lean_dec(v_x_566_);
lean_dec_ref(v_x_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
uint64_t v___y_572_; 
if (lean_obj_tag(v_x_570_) == 0)
{
uint64_t v___x_575_; 
v___x_575_ = 1723ULL;
v___y_572_ = v___x_575_;
goto v___jp_571_;
}
else
{
uint64_t v_hash_576_; 
v_hash_576_ = lean_ctor_get_uint64(v_x_570_, sizeof(void*)*2);
v___y_572_ = v_hash_576_;
goto v___jp_571_;
}
v___jp_571_:
{
size_t v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_uint64_to_usize(v___y_572_);
v___x_574_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(v_x_569_, v___x_573_, v_x_570_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg___boxed(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(v_x_577_, v_x_578_);
lean_dec(v_x_578_);
lean_dec_ref(v_x_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* v_c_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_588_; lean_object* v_decls_589_; lean_object* v___x_590_; 
v___x_588_ = lean_st_ref_get(v_a_586_);
v_decls_589_ = lean_ctor_get(v_a_583_, 2);
v___x_590_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(v_decls_589_, v_c_582_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_env_591_; lean_object* v___x_592_; 
v_env_591_ = lean_ctor_get(v___x_588_, 0);
lean_inc_ref(v_env_591_);
lean_dec(v___x_588_);
lean_inc(v_c_582_);
v___x_592_ = l_Lean_IR_findEnvDecl(v_env_591_, v_c_582_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_593_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
v___x_594_ = 1;
v___x_595_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_582_, v___x_594_);
v___x_596_ = lean_string_append(v___x_593_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
v___x_598_ = lean_string_append(v___x_596_, v___x_597_);
v___x_599_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_598_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
return v___x_599_;
}
else
{
lean_object* v_val_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_c_582_);
v_val_600_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_592_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_val_600_);
lean_dec(v___x_592_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 0);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_val_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_val_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v___x_588_);
lean_dec(v_c_582_);
v_val_608_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_590_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_val_608_);
lean_dec(v___x_590_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 0);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_val_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* v_c_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_IR_Checker_getDecl(v_c_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0(lean_object* v_00_u03b2_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___redArg(v_x_624_, v_x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0___boxed(lean_object* v_00_u03b2_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0(v_00_u03b2_627_, v_x_628_, v_x_629_);
lean_dec(v_x_629_);
lean_dec_ref(v_x_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0(lean_object* v_00_u03b2_631_, lean_object* v_x_632_, size_t v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___redArg(v_x_632_, v_x_633_, v_x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
size_t v_x_1298__boxed_640_; lean_object* v_res_641_; 
v_x_1298__boxed_640_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_res_641_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0(v_00_u03b2_636_, v_x_637_, v_x_1298__boxed_640_, v_x_639_);
lean_dec(v_x_639_);
lean_dec_ref(v_x_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_642_, lean_object* v_keys_643_, lean_object* v_vals_644_, lean_object* v_heq_645_, lean_object* v_i_646_, lean_object* v_k_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___redArg(v_keys_643_, v_vals_644_, v_i_646_, v_k_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_649_, lean_object* v_keys_650_, lean_object* v_vals_651_, lean_object* v_heq_652_, lean_object* v_i_653_, lean_object* v_k_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_Checker_getDecl_spec__0_spec__0_spec__1(v_00_u03b2_649_, v_keys_650_, v_vals_651_, v_heq_652_, v_i_653_, v_k_654_);
lean_dec(v_k_654_);
lean_dec_ref(v_vals_651_);
lean_dec_ref(v_keys_650_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* v_x_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_localCtx_668_; uint8_t v___x_669_; 
v_localCtx_668_ = lean_ctor_get(v_a_660_, 0);
v___x_669_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_668_, v_x_659_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = l_Lean_IR_LocalContext_isParam(v_localCtx_668_, v_x_659_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_671_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_672_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_673_ = l_Nat_reprFast(v_x_659_);
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
lean_dec_ref(v___x_673_);
v___x_675_ = lean_string_append(v___x_671_, v___x_674_);
lean_dec_ref(v___x_674_);
v___x_676_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_677_ = lean_string_append(v___x_675_, v___x_676_);
v___x_678_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_677_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v___x_678_;
}
else
{
lean_dec(v_x_659_);
goto v___jp_665_;
}
}
else
{
lean_dec(v_x_659_);
goto v___jp_665_;
}
v___jp_665_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_IR_Checker_checkVar(v_x_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_localCtx_694_; uint8_t v___x_695_; 
v_localCtx_694_ = lean_ctor_get(v_a_689_, 0);
v___x_695_ = l_Lean_IR_LocalContext_isJP(v_localCtx_694_, v_j_688_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_696_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_697_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_698_ = l_Nat_reprFast(v_j_688_);
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_string_append(v___x_696_, v___x_699_);
lean_dec_ref(v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
v___x_703_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_702_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_j_688_);
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_IR_Checker_checkJP(v_j_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
if (lean_obj_tag(v_a_713_) == 0)
{
lean_object* v_id_719_; lean_object* v___x_720_; 
v_id_719_ = lean_ctor_get(v_a_713_, 0);
lean_inc(v_id_719_);
lean_dec_ref_known(v_a_713_, 1);
v___x_720_ = l_Lean_IR_Checker_checkVar(v_id_719_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_box(0);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_IR_Checker_checkArg(v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_730_, size_t v_i_731_, size_t v_stop_732_, lean_object* v_b_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = lean_usize_dec_eq(v_i_731_, v_stop_732_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_array_uget_borrowed(v_as_730_, v_i_731_);
lean_inc(v___x_740_);
v___x_741_ = l_Lean_IR_Checker_checkArg(v___x_740_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; size_t v___x_743_; size_t v___x_744_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_add(v_i_731_, v___x_743_);
v_i_731_ = v___x_744_;
v_b_733_ = v_a_742_;
goto _start;
}
else
{
return v___x_741_;
}
}
else
{
lean_object* v___x_746_; 
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v_b_733_);
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_747_, lean_object* v_i_748_, lean_object* v_stop_749_, lean_object* v_b_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
size_t v_i_boxed_756_; size_t v_stop_boxed_757_; lean_object* v_res_758_; 
v_i_boxed_756_ = lean_unbox_usize(v_i_748_);
lean_dec(v_i_748_);
v_stop_boxed_757_ = lean_unbox_usize(v_stop_749_);
lean_dec(v_stop_749_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_747_, v_i_boxed_756_, v_stop_boxed_757_, v_b_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec_ref(v_as_747_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_array_get_size(v_as_759_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_nat_dec_lt(v___x_765_, v___x_766_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
return v___x_769_;
}
else
{
size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___x_770_ = ((size_t)0ULL);
v___x_771_ = lean_usize_of_nat(v___x_766_);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_759_, v___x_770_, v___x_771_, v___x_767_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_IR_Checker_checkArgs(v_as_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec_ref(v_as_773_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_781_, lean_object* v_ty_u2082_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_781_, v_ty_u2082_782_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_790_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_789_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
return v___x_790_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_793_, lean_object* v_ty_u2082_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_793_, v_ty_u2082_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_ty_u2082_794_);
lean_dec(v_ty_u2081_793_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_803_, lean_object* v_p_804_, lean_object* v_suffix_x3f_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
lean_inc(v_ty_803_);
v___x_811_ = lean_apply_1(v_p_804_, v_ty_803_);
v___x_812_ = lean_unbox(v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_msg_820_; 
v___x_813_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_814_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_803_);
v___x_815_ = l_Std_Format_defWidth;
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = l_Std_Format_pretty(v___x_814_, v___x_815_, v___x_816_, v___x_816_);
v___x_818_ = lean_string_append(v___x_813_, v___x_817_);
lean_dec_ref(v___x_817_);
v___x_819_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_820_ = lean_string_append(v___x_818_, v___x_819_);
if (lean_obj_tag(v_suffix_x3f_805_) == 1)
{
lean_object* v_val_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_msg_824_; lean_object* v___x_825_; 
v_val_821_ = lean_ctor_get(v_suffix_x3f_805_, 0);
v___x_822_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_823_ = lean_string_append(v_msg_820_, v___x_822_);
v_msg_824_ = lean_string_append(v___x_823_, v_val_821_);
v___x_825_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_824_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_820_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_826_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v_ty_803_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_829_, lean_object* v_p_830_, lean_object* v_suffix_x3f_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_IR_Checker_checkType(v_ty_829_, v_p_830_, v_suffix_x3f_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_suffix_x3f_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = l_Lean_IR_IRType_isObj(v_ty_839_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_msg_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_msg_857_; lean_object* v___x_858_; 
v___x_846_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_847_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_848_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_839_);
v___x_849_ = l_Std_Format_defWidth;
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = l_Std_Format_pretty(v___x_848_, v___x_849_, v___x_850_, v___x_850_);
v___x_852_ = lean_string_append(v___x_847_, v___x_851_);
lean_dec_ref(v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_854_ = lean_string_append(v___x_852_, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_856_ = lean_string_append(v_msg_854_, v___x_855_);
v_msg_857_ = lean_string_append(v___x_856_, v___x_846_);
v___x_858_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_857_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v_ty_839_);
v___x_859_ = lean_box(0);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_IR_Checker_checkObjType(v_ty_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_IR_IRType_isScalar(v_ty_869_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v_msg_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_msg_887_; lean_object* v___x_888_; 
v___x_876_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_877_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_878_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_869_);
v___x_879_ = l_Std_Format_defWidth;
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = l_Std_Format_pretty(v___x_878_, v___x_879_, v___x_880_, v___x_880_);
v___x_882_ = lean_string_append(v___x_877_, v___x_881_);
lean_dec_ref(v___x_881_);
v___x_883_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_884_ = lean_string_append(v___x_882_, v___x_883_);
v___x_885_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_886_ = lean_string_append(v_msg_884_, v___x_885_);
v_msg_887_ = lean_string_append(v___x_886_, v___x_876_);
v___x_888_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_887_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
return v___x_888_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v_ty_869_);
v___x_889_ = lean_box(0);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_IR_Checker_checkScalarType(v_ty_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_localCtx_904_; lean_object* v___x_905_; 
v_localCtx_904_ = lean_ctor_get(v_a_899_, 0);
v___x_905_ = l_Lean_IR_LocalContext_getType(v_localCtx_904_, v_x_898_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_906_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_907_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_908_ = l_Nat_reprFast(v_x_898_);
v___x_909_ = lean_string_append(v___x_907_, v___x_908_);
lean_dec_ref(v___x_908_);
v___x_910_ = lean_string_append(v___x_906_, v___x_909_);
lean_dec_ref(v___x_909_);
v___x_911_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_912_ = lean_string_append(v___x_910_, v___x_911_);
v___x_913_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_912_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_913_;
}
else
{
lean_object* v_val_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_x_898_);
v_val_914_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_905_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_val_914_);
lean_dec(v___x_905_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set_tag(v___x_916_, 0);
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_val_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_IR_Checker_getType(v_x_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_929_, lean_object* v_p_930_, lean_object* v_suffix_x3f_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_IR_Checker_getType(v_x_929_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_962_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_962_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; uint8_t v___x_943_; 
lean_inc(v_a_938_);
v___x_942_ = lean_apply_1(v_p_930_, v_a_938_);
v___x_943_ = lean_unbox(v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_msg_951_; 
lean_del_object(v___x_940_);
v___x_944_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_945_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_938_);
v___x_946_ = l_Std_Format_defWidth;
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = l_Std_Format_pretty(v___x_945_, v___x_946_, v___x_947_, v___x_947_);
v___x_949_ = lean_string_append(v___x_944_, v___x_948_);
lean_dec_ref(v___x_948_);
v___x_950_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_951_ = lean_string_append(v___x_949_, v___x_950_);
if (lean_obj_tag(v_suffix_x3f_931_) == 1)
{
lean_object* v_val_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_msg_955_; lean_object* v___x_956_; 
v_val_952_ = lean_ctor_get(v_suffix_x3f_931_, 0);
v___x_953_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_954_ = lean_string_append(v_msg_951_, v___x_953_);
v_msg_955_ = lean_string_append(v___x_954_, v_val_952_);
v___x_956_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_955_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_951_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_957_;
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec(v_a_938_);
v___x_958_ = lean_box(0);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_958_);
v___x_960_ = v___x_940_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
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
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref(v_p_930_);
v_a_963_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_937_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_937_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_971_, lean_object* v_p_972_, lean_object* v_suffix_x3f_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_IR_Checker_checkVarType(v_x_971_, v_p_972_, v_suffix_x3f_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_suffix_x3f_973_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_987_ = l_Lean_IR_Checker_getType(v_x_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1009_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1009_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1009_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
uint8_t v___x_992_; 
v___x_992_ = l_Lean_IR_IRType_isObj(v_a_988_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_msg_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_msg_1003_; lean_object* v___x_1004_; 
lean_del_object(v___x_990_);
v___x_993_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_994_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_988_);
v___x_995_ = l_Std_Format_defWidth;
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = l_Std_Format_pretty(v___x_994_, v___x_995_, v___x_996_, v___x_996_);
v___x_998_ = lean_string_append(v___x_993_, v___x_997_);
lean_dec_ref(v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1000_ = lean_string_append(v___x_998_, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_1002_ = lean_string_append(v_msg_1000_, v___x_1001_);
v_msg_1003_ = lean_string_append(v___x_1002_, v___x_986_);
v___x_1004_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1003_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_dec(v_a_988_);
v___x_1005_ = lean_box(0);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_1005_);
v___x_1007_ = v___x_990_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_987_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_987_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_IR_Checker_checkObjVar(v_x_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_1032_ = l_Lean_IR_Checker_getType(v_x_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1054_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1054_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1054_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
uint8_t v___x_1037_; 
v___x_1037_ = l_Lean_IR_IRType_isScalar(v_a_1033_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_msg_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_msg_1048_; lean_object* v___x_1049_; 
lean_del_object(v___x_1035_);
v___x_1038_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1039_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1033_);
v___x_1040_ = l_Std_Format_defWidth;
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = l_Std_Format_pretty(v___x_1039_, v___x_1040_, v___x_1041_, v___x_1041_);
v___x_1043_ = lean_string_append(v___x_1038_, v___x_1042_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_1047_ = lean_string_append(v_msg_1045_, v___x_1046_);
v_msg_1048_ = lean_string_append(v___x_1047_, v___x_1031_);
v___x_1049_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1048_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
lean_dec(v_a_1033_);
v___x_1050_ = lean_box(0);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1050_);
v___x_1052_ = v___x_1035_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1032_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1032_);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_IR_Checker_checkScalarVar(v_x_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_1074_, lean_object* v_ys_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___x_1081_; 
lean_inc(v_c_1074_);
v___x_1081_ = l_Lean_IR_Checker_getDecl(v_c_1074_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = lean_array_get_size(v_ys_1075_);
v___x_1084_ = l_Lean_IR_Decl_params(v_a_1082_);
lean_dec(v_a_1082_);
v___x_1085_ = lean_array_get_size(v___x_1084_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = lean_nat_dec_eq(v___x_1083_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1087_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_1088_ = 1;
v___x_1089_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1074_, v___x_1088_);
v___x_1090_ = lean_string_append(v___x_1087_, v___x_1089_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_1092_ = lean_string_append(v___x_1090_, v___x_1091_);
v___x_1093_ = l_Nat_reprFast(v___x_1083_);
v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_1096_ = lean_string_append(v___x_1094_, v___x_1095_);
v___x_1097_ = l_Nat_reprFast(v___x_1085_);
v___x_1098_ = lean_string_append(v___x_1096_, v___x_1097_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_1100_ = lean_string_append(v___x_1098_, v___x_1099_);
v___x_1101_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1100_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
lean_dec(v_c_1074_);
v___x_1102_ = l_Lean_IR_Checker_checkArgs(v_ys_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
return v___x_1102_;
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_c_1074_);
v_a_1103_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1081_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1081_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_1111_, lean_object* v_ys_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_IR_Checker_checkFullApp(v_c_1111_, v_ys_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_ys_1112_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1122_, lean_object* v_ys_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1129_; 
lean_inc(v_c_1122_);
v___x_1129_ = l_Lean_IR_Checker_getDecl(v_c_1122_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = lean_array_get_size(v_ys_1123_);
v___x_1132_ = l_Lean_IR_Decl_params(v_a_1130_);
lean_dec(v_a_1130_);
v___x_1133_ = lean_array_get_size(v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = lean_nat_dec_lt(v___x_1131_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1135_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1136_ = 1;
v___x_1137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1122_, v___x_1136_);
v___x_1138_ = lean_string_append(v___x_1135_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1140_ = lean_string_append(v___x_1138_, v___x_1139_);
v___x_1141_ = l_Nat_reprFast(v___x_1131_);
v___x_1142_ = lean_string_append(v___x_1140_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1143_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1144_ = lean_string_append(v___x_1142_, v___x_1143_);
v___x_1145_ = l_Nat_reprFast(v___x_1133_);
v___x_1146_ = lean_string_append(v___x_1144_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1146_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; 
lean_dec(v_c_1122_);
v___x_1148_ = l_Lean_IR_Checker_checkArgs(v_ys_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
return v___x_1148_;
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_c_1122_);
v_a_1149_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1129_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1129_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
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
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1157_, lean_object* v_ys_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_IR_Checker_checkPartialApp(v_c_1157_, v_ys_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec_ref(v_ys_1158_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1172_, lean_object* v_e_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
switch(lean_obj_tag(v_e_1173_))
{
case 0:
{
lean_object* v_i_1179_; lean_object* v_ys_1180_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v_name_1191_; lean_object* v_cidx_1192_; lean_object* v_size_1193_; lean_object* v_usize_1194_; lean_object* v_ssize_1195_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v_i_1179_ = lean_ctor_get(v_e_1173_, 0);
lean_inc_ref(v_i_1179_);
v_ys_1180_ = lean_ctor_get(v_e_1173_, 1);
lean_inc_ref(v_ys_1180_);
lean_dec_ref_known(v_e_1173_, 2);
v_name_1191_ = lean_ctor_get(v_i_1179_, 0);
v_cidx_1192_ = lean_ctor_get(v_i_1179_, 1);
v_size_1193_ = lean_ctor_get(v_i_1179_, 2);
v_usize_1194_ = lean_ctor_get(v_i_1179_, 3);
v_ssize_1195_ = lean_ctor_get(v_i_1179_, 4);
v___x_1225_ = l_Lean_maxCtorTag;
v___x_1226_ = lean_nat_dec_lt(v___x_1225_, v_cidx_1192_);
if (v___x_1226_ == 0)
{
v___y_1213_ = v_a_1174_;
v___y_1214_ = v_a_1175_;
v___y_1215_ = v_a_1176_;
v___y_1216_ = v_a_1177_;
goto v___jp_1212_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Lean_IR_CtorInfo_isRef(v_i_1179_);
if (v___x_1227_ == 0)
{
v___y_1213_ = v_a_1174_;
v___y_1214_ = v_a_1175_;
v___y_1215_ = v_a_1176_;
v___y_1216_ = v_a_1177_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_inc(v_name_1191_);
lean_dec_ref(v_ys_1180_);
lean_dec_ref(v_i_1179_);
lean_dec(v_ty_1172_);
v___x_1228_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1191_, v___x_1227_);
v___x_1230_ = lean_string_append(v___x_1228_, v___x_1229_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v___x_1233_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1232_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1233_;
}
}
v___jp_1181_:
{
uint8_t v___x_1186_; 
v___x_1186_ = l_Lean_IR_CtorInfo_isRef(v_i_1179_);
lean_dec_ref(v_i_1179_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v_ys_1180_);
lean_dec(v_ty_1172_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref_known(v___x_1189_, 1);
v___x_1190_ = l_Lean_IR_Checker_checkArgs(v_ys_1180_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec_ref(v_ys_1180_);
return v___x_1190_;
}
else
{
lean_dec_ref(v_ys_1180_);
return v___x_1189_;
}
}
}
v___jp_1196_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1201_ = l_Lean_maxCtorScalarsSize;
v___x_1202_ = l_Lean_usizeSize;
v___x_1203_ = lean_nat_mul(v_usize_1194_, v___x_1202_);
v___x_1204_ = lean_nat_add(v_ssize_1195_, v___x_1203_);
lean_dec(v___x_1203_);
v___x_1205_ = lean_nat_dec_lt(v___x_1201_, v___x_1204_);
lean_dec(v___x_1204_);
if (v___x_1205_ == 0)
{
v___y_1182_ = v___y_1197_;
v___y_1183_ = v___y_1198_;
v___y_1184_ = v___y_1199_;
v___y_1185_ = v___y_1200_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_inc(v_name_1191_);
lean_dec_ref(v_ys_1180_);
lean_dec_ref(v_i_1179_);
lean_dec(v_ty_1172_);
v___x_1206_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1191_, v___x_1205_);
v___x_1208_ = lean_string_append(v___x_1206_, v___x_1207_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1210_ = lean_string_append(v___x_1208_, v___x_1209_);
v___x_1211_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1210_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1211_;
}
}
v___jp_1212_:
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = l_Lean_maxCtorNumObjs;
v___x_1218_ = lean_nat_dec_lt(v___x_1217_, v_size_1193_);
if (v___x_1218_ == 0)
{
v___y_1197_ = v___y_1213_;
v___y_1198_ = v___y_1214_;
v___y_1199_ = v___y_1215_;
v___y_1200_ = v___y_1216_;
goto v___jp_1196_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_inc(v_name_1191_);
lean_dec_ref(v_ys_1180_);
lean_dec_ref(v_i_1179_);
lean_dec(v_ty_1172_);
v___x_1219_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1220_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1191_, v___x_1218_);
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1223_ = lean_string_append(v___x_1221_, v___x_1222_);
v___x_1224_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1223_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1224_;
}
}
}
case 1:
{
lean_object* v_x_1234_; lean_object* v___x_1235_; 
v_x_1234_ = lean_ctor_get(v_e_1173_, 1);
lean_inc(v_x_1234_);
lean_dec_ref_known(v_e_1173_, 2);
v___x_1235_ = l_Lean_IR_Checker_checkObjVar(v_x_1234_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref_known(v___x_1235_, 1);
v___x_1236_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1236_;
}
else
{
lean_dec(v_ty_1172_);
return v___x_1235_;
}
}
case 2:
{
lean_object* v_x_1237_; lean_object* v_ys_1238_; lean_object* v___x_1239_; 
v_x_1237_ = lean_ctor_get(v_e_1173_, 0);
lean_inc(v_x_1237_);
v_ys_1238_ = lean_ctor_get(v_e_1173_, 2);
lean_inc_ref(v_ys_1238_);
lean_dec_ref_known(v_e_1173_, 3);
v___x_1239_ = l_Lean_IR_Checker_checkObjVar(v_x_1237_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref_known(v___x_1239_, 1);
v___x_1240_ = l_Lean_IR_Checker_checkArgs(v_ys_1238_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_ys_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1240_, 1);
v___x_1241_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1241_;
}
else
{
lean_dec(v_ty_1172_);
return v___x_1240_;
}
}
else
{
lean_dec_ref(v_ys_1238_);
lean_dec(v_ty_1172_);
return v___x_1239_;
}
}
case 3:
{
lean_object* v_i_1242_; lean_object* v_x_1243_; lean_object* v___x_1244_; 
v_i_1242_ = lean_ctor_get(v_e_1173_, 0);
lean_inc(v_i_1242_);
v_x_1243_ = lean_ctor_get(v_e_1173_, 1);
lean_inc(v_x_1243_);
lean_dec_ref_known(v_e_1173_, 2);
v___x_1244_ = l_Lean_IR_Checker_getType(v_x_1243_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1290_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1290_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1290_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
switch(lean_obj_tag(v_a_1245_))
{
case 7:
{
lean_object* v___x_1249_; 
lean_del_object(v___x_1247_);
lean_dec(v_i_1242_);
v___x_1249_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1249_;
}
case 8:
{
lean_object* v___x_1250_; 
lean_del_object(v___x_1247_);
lean_dec(v_i_1242_);
v___x_1250_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1250_;
}
case 10:
{
lean_object* v_types_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_types_1251_ = lean_ctor_get(v_a_1245_, 1);
lean_inc_ref(v_types_1251_);
lean_dec_ref_known(v_a_1245_, 2);
v___x_1252_ = lean_array_get_size(v_types_1251_);
v___x_1253_ = lean_nat_dec_lt(v_i_1242_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref(v_types_1251_);
lean_del_object(v___x_1247_);
lean_dec(v_i_1242_);
lean_dec(v_ty_1172_);
v___x_1254_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1255_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1254_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1256_ = lean_array_fget(v_types_1251_, v_i_1242_);
lean_dec(v_i_1242_);
lean_dec_ref(v_types_1251_);
v___x_1257_ = l_Lean_IR_instBEqIRType_beq(v___x_1256_, v_ty_1172_);
lean_dec(v_ty_1172_);
lean_dec(v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_del_object(v___x_1247_);
v___x_1258_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1259_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1258_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = lean_box(0);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1260_);
v___x_1262_ = v___x_1247_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
case 11:
{
lean_object* v_types_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_types_1264_ = lean_ctor_get(v_a_1245_, 1);
lean_inc_ref(v_types_1264_);
lean_dec_ref_known(v_a_1245_, 2);
v___x_1265_ = lean_array_get_size(v_types_1264_);
v___x_1266_ = lean_nat_dec_lt(v_i_1242_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec_ref(v_types_1264_);
lean_del_object(v___x_1247_);
lean_dec(v_i_1242_);
lean_dec(v_ty_1172_);
v___x_1267_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1268_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1267_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_array_fget(v_types_1264_, v_i_1242_);
lean_dec(v_i_1242_);
lean_dec_ref(v_types_1264_);
v___x_1270_ = l_Lean_IR_instBEqIRType_beq(v___x_1269_, v_ty_1172_);
lean_dec(v_ty_1172_);
lean_dec(v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_del_object(v___x_1247_);
v___x_1271_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1272_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1271_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = lean_box(0);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1273_);
v___x_1275_ = v___x_1247_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
case 12:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_dec(v_i_1242_);
lean_dec(v_ty_1172_);
v___x_1277_ = lean_box(0);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1277_);
v___x_1279_ = v___x_1247_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
default: 
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_del_object(v___x_1247_);
lean_dec(v_i_1242_);
lean_dec(v_ty_1172_);
v___x_1281_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1282_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1245_);
v___x_1283_ = l_Std_Format_defWidth;
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = l_Std_Format_pretty(v___x_1282_, v___x_1283_, v___x_1284_, v___x_1284_);
v___x_1286_ = lean_string_append(v___x_1281_, v___x_1285_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1288_ = lean_string_append(v___x_1286_, v___x_1287_);
v___x_1289_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1288_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_i_1242_);
lean_dec(v_ty_1172_);
v_a_1291_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1244_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1244_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
case 4:
{
lean_object* v_x_1299_; lean_object* v___x_1300_; 
v_x_1299_ = lean_ctor_get(v_e_1173_, 1);
lean_inc(v_x_1299_);
lean_dec_ref_known(v_e_1173_, 2);
v___x_1300_ = l_Lean_IR_Checker_checkObjVar(v_x_1299_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1319_; 
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v___x_1300_, 0);
lean_dec(v_unused_1320_);
v___x_1302_ = v___x_1300_;
v_isShared_1303_ = v_isSharedCheck_1319_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v___x_1300_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1319_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_box(5);
v___x_1305_ = l_Lean_IR_instBEqIRType_beq(v_ty_1172_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_msg_1313_; lean_object* v___x_1314_; 
lean_del_object(v___x_1302_);
v___x_1306_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1307_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1172_);
v___x_1308_ = l_Std_Format_defWidth;
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = l_Std_Format_pretty(v___x_1307_, v___x_1308_, v___x_1309_, v___x_1309_);
v___x_1311_ = lean_string_append(v___x_1306_, v___x_1310_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1313_ = lean_string_append(v___x_1311_, v___x_1312_);
v___x_1314_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1313_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_dec(v_ty_1172_);
v___x_1315_ = lean_box(0);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1315_);
v___x_1317_ = v___x_1302_;
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
}
else
{
lean_dec(v_ty_1172_);
return v___x_1300_;
}
}
case 5:
{
lean_object* v_x_1321_; lean_object* v___x_1322_; 
v_x_1321_ = lean_ctor_get(v_e_1173_, 2);
lean_inc(v_x_1321_);
lean_dec_ref_known(v_e_1173_, 3);
v___x_1322_ = l_Lean_IR_Checker_checkObjVar(v_x_1321_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1323_; 
lean_dec_ref_known(v___x_1322_, 1);
v___x_1323_ = l_Lean_IR_Checker_checkScalarType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1323_;
}
else
{
lean_dec(v_ty_1172_);
return v___x_1322_;
}
}
case 6:
{
lean_object* v_c_1324_; lean_object* v_ys_1325_; lean_object* v___x_1326_; 
lean_dec(v_ty_1172_);
v_c_1324_ = lean_ctor_get(v_e_1173_, 0);
lean_inc(v_c_1324_);
v_ys_1325_ = lean_ctor_get(v_e_1173_, 1);
lean_inc_ref(v_ys_1325_);
lean_dec_ref_known(v_e_1173_, 2);
v___x_1326_ = l_Lean_IR_Checker_checkFullApp(v_c_1324_, v_ys_1325_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_ys_1325_);
return v___x_1326_;
}
case 7:
{
lean_object* v_c_1327_; lean_object* v_ys_1328_; lean_object* v___x_1329_; 
v_c_1327_ = lean_ctor_get(v_e_1173_, 0);
lean_inc(v_c_1327_);
v_ys_1328_ = lean_ctor_get(v_e_1173_, 1);
lean_inc_ref(v_ys_1328_);
lean_dec_ref_known(v_e_1173_, 2);
v___x_1329_ = l_Lean_IR_Checker_checkPartialApp(v_c_1327_, v_ys_1328_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_ys_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; 
lean_dec_ref_known(v___x_1329_, 1);
v___x_1330_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1330_;
}
else
{
lean_dec(v_ty_1172_);
return v___x_1329_;
}
}
case 8:
{
lean_object* v_x_1331_; lean_object* v_ys_1332_; lean_object* v___x_1333_; 
v_x_1331_ = lean_ctor_get(v_e_1173_, 0);
lean_inc(v_x_1331_);
v_ys_1332_ = lean_ctor_get(v_e_1173_, 1);
lean_inc_ref(v_ys_1332_);
lean_dec_ref_known(v_e_1173_, 2);
v___x_1333_ = l_Lean_IR_Checker_checkObjVar(v_x_1331_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; 
lean_dec_ref_known(v___x_1333_, 1);
v___x_1334_ = l_Lean_IR_Checker_checkArgs(v_ys_1332_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_ys_1332_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v___x_1335_; 
lean_dec_ref_known(v___x_1334_, 1);
v___x_1335_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1335_;
}
else
{
lean_dec(v_ty_1172_);
return v___x_1334_;
}
}
else
{
lean_dec_ref(v_ys_1332_);
lean_dec(v_ty_1172_);
return v___x_1333_;
}
}
case 9:
{
lean_object* v_ty_1336_; lean_object* v_x_1337_; lean_object* v___x_1338_; 
v_ty_1336_ = lean_ctor_get(v_e_1173_, 0);
lean_inc(v_ty_1336_);
v_x_1337_ = lean_ctor_get(v_e_1173_, 1);
lean_inc(v_x_1337_);
lean_dec_ref_known(v_e_1173_, 2);
v___x_1338_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref_known(v___x_1338_, 1);
lean_inc(v_x_1337_);
v___x_1339_ = l_Lean_IR_Checker_checkScalarVar(v_x_1337_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; 
lean_dec_ref_known(v___x_1339_, 1);
v___x_1340_ = l_Lean_IR_Checker_getType(v_x_1337_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1359_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1359_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1359_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_IR_instBEqIRType_beq(v_a_1341_, v_ty_1336_);
lean_dec(v_ty_1336_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_msg_1353_; lean_object* v___x_1354_; 
lean_del_object(v___x_1343_);
v___x_1346_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1347_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1341_);
v___x_1348_ = l_Std_Format_defWidth;
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = l_Std_Format_pretty(v___x_1347_, v___x_1348_, v___x_1349_, v___x_1349_);
v___x_1351_ = lean_string_append(v___x_1346_, v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
v___x_1354_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1353_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_dec(v_a_1341_);
v___x_1355_ = lean_box(0);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1355_);
v___x_1357_ = v___x_1343_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_ty_1336_);
v_a_1360_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1340_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1340_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_dec(v_x_1337_);
lean_dec(v_ty_1336_);
return v___x_1339_;
}
}
else
{
lean_dec(v_x_1337_);
lean_dec(v_ty_1336_);
return v___x_1338_;
}
}
case 10:
{
lean_object* v_x_1368_; lean_object* v___x_1369_; 
v_x_1368_ = lean_ctor_get(v_e_1173_, 0);
lean_inc(v_x_1368_);
lean_dec_ref_known(v_e_1173_, 1);
v___x_1369_ = l_Lean_IR_Checker_checkScalarType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; 
lean_dec_ref_known(v___x_1369_, 1);
v___x_1370_ = l_Lean_IR_Checker_checkObjVar(v_x_1368_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1370_;
}
else
{
lean_dec(v_x_1368_);
return v___x_1369_;
}
}
case 11:
{
lean_object* v_v_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1380_; 
v_v_1371_ = lean_ctor_get(v_e_1173_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_e_1173_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1373_ = v_e_1173_;
v_isShared_1374_ = v_isSharedCheck_1380_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_v_1371_);
lean_dec(v_e_1173_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1380_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
if (lean_obj_tag(v_v_1371_) == 1)
{
lean_object* v___x_1375_; 
lean_dec_ref_known(v_v_1371_, 1);
lean_del_object(v___x_1373_);
v___x_1375_ = l_Lean_IR_Checker_checkObjType(v_ty_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
lean_dec_ref(v_v_1371_);
lean_dec(v_ty_1172_);
v___x_1376_ = lean_box(0);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1376_);
v___x_1378_ = v___x_1373_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
default: 
{
lean_object* v_x_1381_; lean_object* v___x_1382_; 
v_x_1381_ = lean_ctor_get(v_e_1173_, 0);
lean_inc(v_x_1381_);
lean_dec_ref_known(v_e_1173_, 1);
v___x_1382_ = l_Lean_IR_Checker_checkObjVar(v_x_1381_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1401_; 
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1382_, 0);
lean_dec(v_unused_1402_);
v___x_1384_ = v___x_1382_;
v_isShared_1385_ = v_isSharedCheck_1401_;
goto v_resetjp_1383_;
}
else
{
lean_dec(v___x_1382_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1401_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = lean_box(1);
v___x_1387_ = l_Lean_IR_instBEqIRType_beq(v_ty_1172_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_msg_1395_; lean_object* v___x_1396_; 
lean_del_object(v___x_1384_);
v___x_1388_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1389_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1172_);
v___x_1390_ = l_Std_Format_defWidth;
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = l_Std_Format_pretty(v___x_1389_, v___x_1390_, v___x_1391_, v___x_1391_);
v___x_1393_ = lean_string_append(v___x_1388_, v___x_1392_);
lean_dec_ref(v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
v___x_1396_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1395_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_dec(v_ty_1172_);
v___x_1397_ = lean_box(0);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1397_);
v___x_1399_ = v___x_1384_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_dec(v_ty_1172_);
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1403_, lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_IR_Checker_checkExpr(v_ty_1403_, v_e_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1411_, lean_object* v_p_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_x_1418_; lean_object* v___x_1419_; 
v_x_1418_ = lean_ctor_get(v_p_1412_, 0);
lean_inc(v_x_1418_);
v___x_1419_ = l_Lean_IR_Checker_markVar(v_x_1418_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1427_; 
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v___x_1419_, 0);
lean_dec(v_unused_1428_);
v___x_1421_ = v___x_1419_;
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v___x_1419_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = l_Lean_IR_LocalContext_addParam(v_ctx_1411_, v_p_1412_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1423_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec_ref(v_p_1412_);
lean_dec_ref(v_ctx_1411_);
v_a_1429_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1419_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1419_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1437_, lean_object* v_p_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1437_, v_p_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1444_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_instMonadEIO___redArg();
return v___x_1445_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1447_ = l_StateRefT_x27_instMonad___redArg(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1451_, lean_object* v_k_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v_toApplicative_1459_; lean_object* v_toFunctor_1460_; lean_object* v_toSeq_1461_; lean_object* v_toSeqLeft_1462_; lean_object* v_toSeqRight_1463_; lean_object* v___f_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v_localCtx_1476_; lean_object* v_currentDecl_1477_; lean_object* v_decls_1478_; lean_object* v_a_1480_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1458_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1459_ = lean_ctor_get(v___x_1458_, 0);
v_toFunctor_1460_ = lean_ctor_get(v_toApplicative_1459_, 0);
v_toSeq_1461_ = lean_ctor_get(v_toApplicative_1459_, 2);
v_toSeqLeft_1462_ = lean_ctor_get(v_toApplicative_1459_, 3);
v_toSeqRight_1463_ = lean_ctor_get(v_toApplicative_1459_, 4);
v___f_1464_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1465_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1460_, 2);
v___f_1466_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1466_, 0, v_toFunctor_1460_);
v___f_1467_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1467_, 0, v_toFunctor_1460_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___f_1466_);
lean_ctor_set(v___x_1468_, 1, v___f_1467_);
lean_inc(v_toSeqRight_1463_);
v___f_1469_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1469_, 0, v_toSeqRight_1463_);
lean_inc(v_toSeqLeft_1462_);
v___f_1470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1470_, 0, v_toSeqLeft_1462_);
lean_inc(v_toSeq_1461_);
v___f_1471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1471_, 0, v_toSeq_1461_);
v___x_1472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1468_);
lean_ctor_set(v___x_1472_, 1, v___f_1464_);
lean_ctor_set(v___x_1472_, 2, v___f_1471_);
lean_ctor_set(v___x_1472_, 3, v___f_1470_);
lean_ctor_set(v___x_1472_, 4, v___f_1469_);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___f_1465_);
v___x_1474_ = l_StateRefT_x27_instMonad___redArg(v___x_1473_);
v___x_1475_ = l_ReaderT_instMonad___redArg(v___x_1474_);
v_localCtx_1476_ = lean_ctor_get(v_a_1453_, 0);
v_currentDecl_1477_ = lean_ctor_get(v_a_1453_, 1);
v_decls_1478_ = lean_ctor_get(v_a_1453_, 2);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_array_get_size(v_ps_1451_);
v___x_1485_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_dec_ref(v___x_1475_);
lean_dec_ref(v_ps_1451_);
lean_inc_ref(v_localCtx_1476_);
v_a_1480_ = v_localCtx_1476_;
goto v___jp_1479_;
}
else
{
lean_object* v___f_1486_; size_t v___x_1487_; size_t v___x_1488_; lean_object* v___x_1038__overap_1489_; lean_object* v___x_1490_; 
v___f_1486_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = lean_usize_of_nat(v___x_1484_);
lean_inc_ref(v_localCtx_1476_);
v___x_1038__overap_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1475_, v___f_1486_, v_ps_1451_, v___x_1487_, v___x_1488_, v_localCtx_1476_);
lean_inc(v_a_1456_);
lean_inc_ref(v_a_1455_);
lean_inc(v_a_1454_);
lean_inc_ref(v_a_1453_);
v___x_1490_ = lean_apply_5(v___x_1038__overap_1489_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, lean_box(0));
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v_a_1480_ = v_a_1491_;
goto v___jp_1479_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v_k_1452_);
v_a_1492_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1490_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1490_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
v___jp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_inc_ref(v_decls_1478_);
lean_inc_ref(v_currentDecl_1477_);
v___x_1481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1481_, 0, v_a_1480_);
lean_ctor_set(v___x_1481_, 1, v_currentDecl_1477_);
lean_ctor_set(v___x_1481_, 2, v_decls_1478_);
lean_inc(v_a_1456_);
lean_inc_ref(v_a_1455_);
lean_inc(v_a_1454_);
v___x_1482_ = lean_apply_5(v_k_1452_, v___x_1481_, v_a_1454_, v_a_1455_, v_a_1456_, lean_box(0));
return v___x_1482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1500_, lean_object* v_k_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_IR_Checker_withParams(v_ps_1500_, v_k_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1508_, size_t v_i_1509_, size_t v_stop_1510_, lean_object* v_b_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_usize_dec_eq(v_i_1509_, v_stop_1510_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v_x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = lean_array_uget_borrowed(v_as_1508_, v_i_1509_);
v_x_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_x_1519_);
v___x_1520_ = l_Lean_IR_Checker_markVar(v_x_1519_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1521_; size_t v___x_1522_; size_t v___x_1523_; 
lean_dec_ref_known(v___x_1520_, 1);
lean_inc(v___x_1518_);
v___x_1521_ = l_Lean_IR_LocalContext_addParam(v_b_1511_, v___x_1518_);
v___x_1522_ = ((size_t)1ULL);
v___x_1523_ = lean_usize_add(v_i_1509_, v___x_1522_);
v_i_1509_ = v___x_1523_;
v_b_1511_ = v___x_1521_;
goto _start;
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v_b_1511_);
v_a_1525_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1520_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1520_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_b_1511_);
return v___x_1533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1534_, lean_object* v_i_1535_, lean_object* v_stop_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
size_t v_i_boxed_1543_; size_t v_stop_boxed_1544_; lean_object* v_res_1545_; 
v_i_boxed_1543_ = lean_unbox_usize(v_i_1535_);
lean_dec(v_i_1535_);
v_stop_boxed_1544_ = lean_unbox_usize(v_stop_1536_);
lean_dec(v_stop_1536_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1534_, v_i_boxed_1543_, v_stop_boxed_1544_, v_b_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec_ref(v_as_1534_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_x_1553_; lean_object* v_b_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; 
switch(lean_obj_tag(v_fnBody_1546_))
{
case 0:
{
lean_object* v_x_1561_; lean_object* v_ty_1562_; lean_object* v_e_1563_; lean_object* v_b_1564_; lean_object* v___x_1565_; 
v_x_1561_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_x_1561_);
v_ty_1562_ = lean_ctor_get(v_fnBody_1546_, 1);
lean_inc_n(v_ty_1562_, 2);
v_e_1563_ = lean_ctor_get(v_fnBody_1546_, 2);
lean_inc_ref_n(v_e_1563_, 2);
v_b_1564_ = lean_ctor_get(v_fnBody_1546_, 3);
lean_inc(v_b_1564_);
lean_dec_ref_known(v_fnBody_1546_, 4);
v___x_1565_ = l_Lean_IR_Checker_checkExpr(v_ty_1562_, v_e_1563_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; 
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v_x_1561_);
v___x_1566_ = l_Lean_IR_Checker_markVar(v_x_1561_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_localCtx_1567_; lean_object* v_currentDecl_1568_; lean_object* v_decls_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref_known(v___x_1566_, 1);
v_localCtx_1567_ = lean_ctor_get(v_a_1547_, 0);
lean_inc_ref(v_localCtx_1567_);
v_currentDecl_1568_ = lean_ctor_get(v_a_1547_, 1);
lean_inc_ref(v_currentDecl_1568_);
v_decls_1569_ = lean_ctor_get(v_a_1547_, 2);
lean_inc_ref(v_decls_1569_);
lean_dec_ref(v_a_1547_);
v___x_1570_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1567_, v_x_1561_, v_ty_1562_, v_e_1563_);
v___x_1571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v_currentDecl_1568_);
lean_ctor_set(v___x_1571_, 2, v_decls_1569_);
v_fnBody_1546_ = v_b_1564_;
v_a_1547_ = v___x_1571_;
goto _start;
}
else
{
lean_dec(v_b_1564_);
lean_dec_ref(v_e_1563_);
lean_dec(v_ty_1562_);
lean_dec(v_x_1561_);
lean_dec_ref(v_a_1547_);
return v___x_1566_;
}
}
else
{
lean_dec(v_b_1564_);
lean_dec_ref(v_e_1563_);
lean_dec(v_ty_1562_);
lean_dec(v_x_1561_);
lean_dec_ref(v_a_1547_);
return v___x_1565_;
}
}
case 1:
{
lean_object* v_j_1573_; lean_object* v_xs_1574_; lean_object* v_v_1575_; lean_object* v_b_1576_; lean_object* v_a_1578_; lean_object* v___x_1587_; 
v_j_1573_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc_n(v_j_1573_, 2);
v_xs_1574_ = lean_ctor_get(v_fnBody_1546_, 1);
lean_inc_ref(v_xs_1574_);
v_v_1575_ = lean_ctor_get(v_fnBody_1546_, 2);
lean_inc(v_v_1575_);
v_b_1576_ = lean_ctor_get(v_fnBody_1546_, 3);
lean_inc(v_b_1576_);
lean_dec_ref_known(v_fnBody_1546_, 4);
v___x_1587_ = l_Lean_IR_Checker_markJP(v_j_1573_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_localCtx_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
lean_dec_ref_known(v___x_1587_, 1);
v_localCtx_1588_ = lean_ctor_get(v_a_1547_, 0);
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = lean_array_get_size(v_xs_1574_);
v___x_1591_ = lean_nat_dec_lt(v___x_1589_, v___x_1590_);
if (v___x_1591_ == 0)
{
lean_inc_ref(v_localCtx_1588_);
v_a_1578_ = v_localCtx_1588_;
goto v___jp_1577_;
}
else
{
size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = lean_usize_of_nat(v___x_1590_);
lean_inc_ref(v_localCtx_1588_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1574_, v___x_1592_, v___x_1593_, v_localCtx_1588_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v_a_1578_ = v_a_1595_;
goto v___jp_1577_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_b_1576_);
lean_dec(v_v_1575_);
lean_dec_ref(v_xs_1574_);
lean_dec(v_j_1573_);
lean_dec_ref(v_a_1547_);
v_a_1596_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1594_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
else
{
lean_dec(v_b_1576_);
lean_dec(v_v_1575_);
lean_dec_ref(v_xs_1574_);
lean_dec(v_j_1573_);
lean_dec_ref(v_a_1547_);
return v___x_1587_;
}
v___jp_1577_:
{
lean_object* v_localCtx_1579_; lean_object* v_currentDecl_1580_; lean_object* v_decls_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_localCtx_1579_ = lean_ctor_get(v_a_1547_, 0);
lean_inc_ref(v_localCtx_1579_);
v_currentDecl_1580_ = lean_ctor_get(v_a_1547_, 1);
lean_inc_ref_n(v_currentDecl_1580_, 2);
v_decls_1581_ = lean_ctor_get(v_a_1547_, 2);
lean_inc_ref_n(v_decls_1581_, 2);
lean_dec_ref(v_a_1547_);
v___x_1582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1582_, 0, v_a_1578_);
lean_ctor_set(v___x_1582_, 1, v_currentDecl_1580_);
lean_ctor_set(v___x_1582_, 2, v_decls_1581_);
lean_inc(v_v_1575_);
v___x_1583_ = l_Lean_IR_Checker_checkFnBody(v_v_1575_, v___x_1582_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref_known(v___x_1583_, 1);
v___x_1584_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1579_, v_j_1573_, v_xs_1574_, v_v_1575_);
v___x_1585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v_currentDecl_1580_);
lean_ctor_set(v___x_1585_, 2, v_decls_1581_);
v_fnBody_1546_ = v_b_1576_;
v_a_1547_ = v___x_1585_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1581_);
lean_dec_ref(v_currentDecl_1580_);
lean_dec_ref(v_localCtx_1579_);
lean_dec(v_b_1576_);
lean_dec(v_v_1575_);
lean_dec_ref(v_xs_1574_);
lean_dec(v_j_1573_);
return v___x_1583_;
}
}
}
case 2:
{
lean_object* v_x_1604_; lean_object* v_y_1605_; lean_object* v_b_1606_; lean_object* v___x_1607_; 
v_x_1604_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_x_1604_);
v_y_1605_ = lean_ctor_get(v_fnBody_1546_, 2);
lean_inc(v_y_1605_);
v_b_1606_ = lean_ctor_get(v_fnBody_1546_, 3);
lean_inc(v_b_1606_);
lean_dec_ref_known(v_fnBody_1546_, 4);
v___x_1607_ = l_Lean_IR_Checker_checkVar(v_x_1604_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref_known(v___x_1607_, 1);
v___x_1608_ = l_Lean_IR_Checker_checkArg(v_y_1605_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_dec_ref_known(v___x_1608_, 1);
v_fnBody_1546_ = v_b_1606_;
goto _start;
}
else
{
lean_dec(v_b_1606_);
lean_dec_ref(v_a_1547_);
return v___x_1608_;
}
}
else
{
lean_dec(v_b_1606_);
lean_dec(v_y_1605_);
lean_dec_ref(v_a_1547_);
return v___x_1607_;
}
}
case 3:
{
lean_object* v_x_1610_; lean_object* v_b_1611_; lean_object* v___x_1612_; 
v_x_1610_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_x_1610_);
v_b_1611_ = lean_ctor_get(v_fnBody_1546_, 2);
lean_inc(v_b_1611_);
lean_dec_ref_known(v_fnBody_1546_, 3);
v___x_1612_ = l_Lean_IR_Checker_checkVar(v_x_1610_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_dec_ref_known(v___x_1612_, 1);
v_fnBody_1546_ = v_b_1611_;
goto _start;
}
else
{
lean_dec(v_b_1611_);
lean_dec_ref(v_a_1547_);
return v___x_1612_;
}
}
case 4:
{
lean_object* v_x_1614_; lean_object* v_y_1615_; lean_object* v_b_1616_; lean_object* v___x_1617_; 
v_x_1614_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_x_1614_);
v_y_1615_ = lean_ctor_get(v_fnBody_1546_, 2);
lean_inc(v_y_1615_);
v_b_1616_ = lean_ctor_get(v_fnBody_1546_, 3);
lean_inc(v_b_1616_);
lean_dec_ref_known(v_fnBody_1546_, 4);
v___x_1617_ = l_Lean_IR_Checker_checkVar(v_x_1614_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v___x_1618_; 
lean_dec_ref_known(v___x_1617_, 1);
v___x_1618_ = l_Lean_IR_Checker_checkVar(v_y_1615_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_dec_ref_known(v___x_1618_, 1);
v_fnBody_1546_ = v_b_1616_;
goto _start;
}
else
{
lean_dec(v_b_1616_);
lean_dec_ref(v_a_1547_);
return v___x_1618_;
}
}
else
{
lean_dec(v_b_1616_);
lean_dec(v_y_1615_);
lean_dec_ref(v_a_1547_);
return v___x_1617_;
}
}
case 5:
{
lean_object* v_x_1620_; lean_object* v_y_1621_; lean_object* v_b_1622_; lean_object* v___x_1623_; 
v_x_1620_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_x_1620_);
v_y_1621_ = lean_ctor_get(v_fnBody_1546_, 3);
lean_inc(v_y_1621_);
v_b_1622_ = lean_ctor_get(v_fnBody_1546_, 5);
lean_inc(v_b_1622_);
lean_dec_ref_known(v_fnBody_1546_, 6);
v___x_1623_ = l_Lean_IR_Checker_checkVar(v_x_1620_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1624_; 
lean_dec_ref_known(v___x_1623_, 1);
v___x_1624_ = l_Lean_IR_Checker_checkVar(v_y_1621_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_dec_ref_known(v___x_1624_, 1);
v_fnBody_1546_ = v_b_1622_;
goto _start;
}
else
{
lean_dec(v_b_1622_);
lean_dec_ref(v_a_1547_);
return v___x_1624_;
}
}
else
{
lean_dec(v_b_1622_);
lean_dec(v_y_1621_);
lean_dec_ref(v_a_1547_);
return v___x_1623_;
}
}
case 8:
{
lean_object* v_x_1626_; lean_object* v_b_1627_; lean_object* v___x_1628_; 
v_x_1626_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_x_1626_);
v_b_1627_ = lean_ctor_get(v_fnBody_1546_, 1);
lean_inc(v_b_1627_);
lean_dec_ref_known(v_fnBody_1546_, 2);
v___x_1628_ = l_Lean_IR_Checker_checkVar(v_x_1626_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_dec_ref_known(v___x_1628_, 1);
v_fnBody_1546_ = v_b_1627_;
goto _start;
}
else
{
lean_dec(v_b_1627_);
lean_dec_ref(v_a_1547_);
return v___x_1628_;
}
}
case 9:
{
lean_object* v_x_1630_; lean_object* v_cs_1631_; lean_object* v___x_1632_; 
v_x_1630_ = lean_ctor_get(v_fnBody_1546_, 1);
lean_inc(v_x_1630_);
v_cs_1631_ = lean_ctor_get(v_fnBody_1546_, 3);
lean_inc_ref(v_cs_1631_);
lean_dec_ref_known(v_fnBody_1546_, 4);
v___x_1632_ = l_Lean_IR_Checker_checkVar(v_x_1630_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1646_; 
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v___x_1632_, 0);
lean_dec(v_unused_1647_);
v___x_1634_ = v___x_1632_;
v_isShared_1635_ = v_isSharedCheck_1646_;
goto v_resetjp_1633_;
}
else
{
lean_dec(v___x_1632_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1646_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = lean_array_get_size(v_cs_1631_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_nat_dec_lt(v___x_1636_, v___x_1637_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref(v_cs_1631_);
lean_dec_ref(v_a_1547_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1638_);
v___x_1641_ = v___x_1634_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1638_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
lean_del_object(v___x_1634_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = lean_usize_of_nat(v___x_1637_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1631_, v___x_1643_, v___x_1644_, v___x_1638_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec_ref(v_a_1547_);
lean_dec_ref(v_cs_1631_);
return v___x_1645_;
}
}
}
else
{
lean_dec_ref(v_cs_1631_);
lean_dec_ref(v_a_1547_);
return v___x_1632_;
}
}
case 10:
{
lean_object* v_x_1648_; lean_object* v___x_1649_; 
v_x_1648_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_x_1648_);
lean_dec_ref_known(v_fnBody_1546_, 1);
v___x_1649_ = l_Lean_IR_Checker_checkArg(v_x_1648_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec_ref(v_a_1547_);
return v___x_1649_;
}
case 11:
{
lean_object* v_j_1650_; lean_object* v_ys_1651_; lean_object* v___x_1652_; 
v_j_1650_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_j_1650_);
v_ys_1651_ = lean_ctor_get(v_fnBody_1546_, 1);
lean_inc_ref(v_ys_1651_);
lean_dec_ref_known(v_fnBody_1546_, 2);
v___x_1652_ = l_Lean_IR_Checker_checkJP(v_j_1650_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref_known(v___x_1652_, 1);
v___x_1653_ = l_Lean_IR_Checker_checkArgs(v_ys_1651_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec_ref(v_a_1547_);
lean_dec_ref(v_ys_1651_);
return v___x_1653_;
}
else
{
lean_dec_ref(v_ys_1651_);
lean_dec_ref(v_a_1547_);
return v___x_1652_;
}
}
case 12:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec_ref(v_a_1547_);
v___x_1654_ = lean_box(0);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
default: 
{
lean_object* v_x_1656_; lean_object* v_b_1657_; 
v_x_1656_ = lean_ctor_get(v_fnBody_1546_, 0);
lean_inc(v_x_1656_);
v_b_1657_ = lean_ctor_get(v_fnBody_1546_, 2);
lean_inc(v_b_1657_);
lean_dec(v_fnBody_1546_);
v_x_1553_ = v_x_1656_;
v_b_1554_ = v_b_1657_;
v___y_1555_ = v_a_1547_;
v___y_1556_ = v_a_1548_;
v___y_1557_ = v_a_1549_;
v___y_1558_ = v_a_1550_;
goto v___jp_1552_;
}
}
v___jp_1552_:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_IR_Checker_checkVar(v_x_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_dec_ref_known(v___x_1559_, 1);
v_fnBody_1546_ = v_b_1554_;
v_a_1547_ = v___y_1555_;
v_a_1548_ = v___y_1556_;
v_a_1549_ = v___y_1557_;
v_a_1550_ = v___y_1558_;
goto _start;
}
else
{
lean_dec_ref(v___y_1555_);
lean_dec(v_b_1554_);
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1658_, size_t v_i_1659_, size_t v_stop_1660_, lean_object* v_b_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_usize_dec_eq(v_i_1659_, v_stop_1660_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_array_uget_borrowed(v_as_1658_, v_i_1659_);
v___x_1669_ = l_Lean_IR_Alt_body(v___x_1668_);
lean_inc_ref(v___y_1662_);
v___x_1670_ = l_Lean_IR_Checker_checkFnBody(v___x_1669_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; size_t v___x_1672_; size_t v___x_1673_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1659_, v___x_1672_);
v_i_1659_ = v___x_1673_;
v_b_1661_ = v_a_1671_;
goto _start;
}
else
{
return v___x_1670_;
}
}
else
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v_b_1661_);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1676_, lean_object* v_i_1677_, lean_object* v_stop_1678_, lean_object* v_b_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
size_t v_i_boxed_1685_; size_t v_stop_boxed_1686_; lean_object* v_res_1687_; 
v_i_boxed_1685_ = lean_unbox_usize(v_i_1677_);
lean_dec(v_i_1677_);
v_stop_boxed_1686_ = lean_unbox_usize(v_stop_1678_);
lean_dec(v_stop_1678_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1676_, v_i_boxed_1685_, v_stop_boxed_1686_, v_b_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v_as_1676_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
if (lean_obj_tag(v_x_1695_) == 0)
{
lean_object* v_xs_1701_; lean_object* v_body_1702_; lean_object* v_localCtx_1703_; lean_object* v_currentDecl_1704_; lean_object* v_decls_1705_; lean_object* v_a_1707_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_xs_1701_ = lean_ctor_get(v_x_1695_, 1);
lean_inc_ref(v_xs_1701_);
v_body_1702_ = lean_ctor_get(v_x_1695_, 3);
lean_inc(v_body_1702_);
lean_dec_ref_known(v_x_1695_, 5);
v_localCtx_1703_ = lean_ctor_get(v_a_1696_, 0);
v_currentDecl_1704_ = lean_ctor_get(v_a_1696_, 1);
v_decls_1705_ = lean_ctor_get(v_a_1696_, 2);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_array_get_size(v_xs_1701_);
v___x_1712_ = lean_nat_dec_lt(v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_dec_ref(v_xs_1701_);
lean_inc_ref(v_localCtx_1703_);
v_a_1707_ = v_localCtx_1703_;
goto v___jp_1706_;
}
else
{
size_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = lean_usize_of_nat(v___x_1711_);
lean_inc_ref(v_localCtx_1703_);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1701_, v___x_1713_, v___x_1714_, v_localCtx_1703_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec_ref(v_xs_1701_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v_a_1707_ = v_a_1716_;
goto v___jp_1706_;
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_body_1702_);
v_a_1717_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1715_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
v___jp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_inc_ref(v_decls_1705_);
lean_inc_ref(v_currentDecl_1704_);
v___x_1708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1708_, 0, v_a_1707_);
lean_ctor_set(v___x_1708_, 1, v_currentDecl_1704_);
lean_ctor_set(v___x_1708_, 2, v_decls_1705_);
v___x_1709_ = l_Lean_IR_Checker_checkFnBody(v_body_1702_, v___x_1708_, v_a_1697_, v_a_1698_, v_a_1699_);
return v___x_1709_;
}
}
else
{
lean_object* v_xs_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_xs_1725_ = lean_ctor_get(v_x_1695_, 1);
lean_inc_ref(v_xs_1725_);
lean_dec_ref_known(v_x_1695_, 4);
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_array_get_size(v_xs_1725_);
v___x_1729_ = lean_nat_dec_lt(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v_xs_1725_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1726_);
return v___x_1730_;
}
else
{
lean_object* v_localCtx_1731_; size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v_localCtx_1731_ = lean_ctor_get(v_a_1696_, 0);
v___x_1732_ = ((size_t)0ULL);
v___x_1733_ = lean_usize_of_nat(v___x_1728_);
lean_inc_ref(v_localCtx_1731_);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1725_, v___x_1732_, v___x_1733_, v_localCtx_1731_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec_ref(v_xs_1725_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1734_, 0);
lean_dec(v_unused_1742_);
v___x_1736_ = v___x_1734_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v___x_1734_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1726_);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1726_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
v_a_1743_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1734_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1734_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_IR_Checker_checkDecl(v_x_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v_ks_1762_; lean_object* v_vs_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1787_; 
v_ks_1762_ = lean_ctor_get(v_x_1758_, 0);
v_vs_1763_ = lean_ctor_get(v_x_1758_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_x_1758_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1765_ = v_x_1758_;
v_isShared_1766_ = v_isSharedCheck_1787_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_vs_1763_);
lean_inc(v_ks_1762_);
lean_dec(v_x_1758_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1787_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_array_get_size(v_ks_1762_);
v___x_1768_ = lean_nat_dec_lt(v_x_1759_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_dec(v_x_1759_);
v___x_1769_ = lean_array_push(v_ks_1762_, v_x_1760_);
v___x_1770_ = lean_array_push(v_vs_1763_, v_x_1761_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1770_);
lean_ctor_set(v___x_1765_, 0, v___x_1769_);
v___x_1772_ = v___x_1765_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
else
{
lean_object* v_k_x27_1774_; uint8_t v___x_1775_; 
v_k_x27_1774_ = lean_array_fget_borrowed(v_ks_1762_, v_x_1759_);
v___x_1775_ = lean_name_eq(v_x_1760_, v_k_x27_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1777_; 
if (v_isShared_1766_ == 0)
{
v___x_1777_ = v___x_1765_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_ks_1762_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_vs_1763_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_x_1759_, v___x_1778_);
lean_dec(v_x_1759_);
v_x_1758_ = v___x_1777_;
v_x_1759_ = v___x_1779_;
goto _start;
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_array_fset(v_ks_1762_, v_x_1759_, v_x_1760_);
v___x_1783_ = lean_array_fset(v_vs_1763_, v_x_1759_, v_x_1761_);
lean_dec(v_x_1759_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1783_);
lean_ctor_set(v___x_1765_, 0, v___x_1782_);
v___x_1785_ = v___x_1765_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1788_, lean_object* v_k_1789_, lean_object* v_v_1790_){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1788_, v___x_1791_, v_k_1789_, v_v_1790_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(lean_object* v_x_1794_, size_t v_x_1795_, size_t v_x_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v_es_1799_; size_t v___x_1800_; size_t v___x_1801_; lean_object* v_j_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_es_1799_ = lean_ctor_get(v_x_1794_, 0);
v___x_1800_ = ((size_t)31ULL);
v___x_1801_ = lean_usize_land(v_x_1795_, v___x_1800_);
v_j_1802_ = lean_usize_to_nat(v___x_1801_);
v___x_1803_ = lean_array_get_size(v_es_1799_);
v___x_1804_ = lean_nat_dec_lt(v_j_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec(v_j_1802_);
lean_dec(v_x_1798_);
lean_dec(v_x_1797_);
return v_x_1794_;
}
else
{
lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1843_; 
lean_inc_ref(v_es_1799_);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_x_1794_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_x_1794_, 0);
lean_dec(v_unused_1844_);
v___x_1806_ = v_x_1794_;
v_isShared_1807_ = v_isSharedCheck_1843_;
goto v_resetjp_1805_;
}
else
{
lean_dec(v_x_1794_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1843_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_v_1808_; lean_object* v___x_1809_; lean_object* v_xs_x27_1810_; lean_object* v___y_1812_; 
v_v_1808_ = lean_array_fget(v_es_1799_, v_j_1802_);
v___x_1809_ = lean_box(0);
v_xs_x27_1810_ = lean_array_fset(v_es_1799_, v_j_1802_, v___x_1809_);
switch(lean_obj_tag(v_v_1808_))
{
case 0:
{
lean_object* v_key_1817_; lean_object* v_val_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1828_; 
v_key_1817_ = lean_ctor_get(v_v_1808_, 0);
v_val_1818_ = lean_ctor_get(v_v_1808_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_v_1808_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1820_ = v_v_1808_;
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_val_1818_);
lean_inc(v_key_1817_);
lean_dec(v_v_1808_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_name_eq(v_x_1797_, v_key_1817_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_del_object(v___x_1820_);
v___x_1823_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1817_, v_val_1818_, v_x_1797_, v_x_1798_);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
v___y_1812_ = v___x_1824_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1826_; 
lean_dec(v_val_1818_);
lean_dec(v_key_1817_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v_x_1798_);
lean_ctor_set(v___x_1820_, 0, v_x_1797_);
v___x_1826_ = v___x_1820_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_x_1797_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_x_1798_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
v___y_1812_ = v___x_1826_;
goto v___jp_1811_;
}
}
}
}
case 1:
{
lean_object* v_node_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1841_; 
v_node_1829_ = lean_ctor_get(v_v_1808_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_v_1808_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1831_ = v_v_1808_;
v_isShared_1832_ = v_isSharedCheck_1841_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_node_1829_);
lean_dec(v_v_1808_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1841_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
size_t v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1833_ = ((size_t)5ULL);
v___x_1834_ = lean_usize_shift_right(v_x_1795_, v___x_1833_);
v___x_1835_ = ((size_t)1ULL);
v___x_1836_ = lean_usize_add(v_x_1796_, v___x_1835_);
v___x_1837_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_node_1829_, v___x_1834_, v___x_1836_, v_x_1797_, v_x_1798_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1837_);
v___x_1839_ = v___x_1831_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v___y_1812_ = v___x_1839_;
goto v___jp_1811_;
}
}
}
default: 
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_x_1797_);
lean_ctor_set(v___x_1842_, 1, v_x_1798_);
v___y_1812_ = v___x_1842_;
goto v___jp_1811_;
}
}
v___jp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1813_ = lean_array_fset(v_xs_x27_1810_, v_j_1802_, v___y_1812_);
lean_dec(v_j_1802_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1813_);
v___x_1815_ = v___x_1806_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
else
{
lean_object* v_ks_1845_; lean_object* v_vs_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1864_; 
v_ks_1845_ = lean_ctor_get(v_x_1794_, 0);
v_vs_1846_ = lean_ctor_get(v_x_1794_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_x_1794_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1848_ = v_x_1794_;
v_isShared_1849_ = v_isSharedCheck_1864_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_vs_1846_);
lean_inc(v_ks_1845_);
lean_dec(v_x_1794_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1864_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_ks_1845_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_vs_1846_);
v___x_1851_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v_newNode_1852_; size_t v___x_1853_; uint8_t v___x_1854_; 
v_newNode_1852_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1___redArg(v___x_1851_, v_x_1797_, v_x_1798_);
v___x_1853_ = ((size_t)7ULL);
v___x_1854_ = lean_usize_dec_le(v___x_1853_, v_x_1796_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1855_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1852_);
v___x_1856_ = lean_unsigned_to_nat(4u);
v___x_1857_ = lean_nat_dec_lt(v___x_1855_, v___x_1856_);
lean_dec(v___x_1855_);
if (v___x_1857_ == 0)
{
lean_object* v_ks_1858_; lean_object* v_vs_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_ks_1858_ = lean_ctor_get(v_newNode_1852_, 0);
lean_inc_ref(v_ks_1858_);
v_vs_1859_ = lean_ctor_get(v_newNode_1852_, 1);
lean_inc_ref(v_vs_1859_);
lean_dec_ref(v_newNode_1852_);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___closed__0);
v___x_1862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(v_x_1796_, v_ks_1858_, v_vs_1859_, v___x_1860_, v___x_1861_);
lean_dec_ref(v_vs_1859_);
lean_dec_ref(v_ks_1858_);
return v___x_1862_;
}
else
{
return v_newNode_1852_;
}
}
else
{
return v_newNode_1852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(size_t v_depth_1865_, lean_object* v_keys_1866_, lean_object* v_vals_1867_, lean_object* v_i_1868_, lean_object* v_entries_1869_){
_start:
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_array_get_size(v_keys_1866_);
v___x_1871_ = lean_nat_dec_lt(v_i_1868_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_dec(v_i_1868_);
return v_entries_1869_;
}
else
{
lean_object* v_k_1872_; lean_object* v_v_1873_; uint64_t v___y_1875_; 
v_k_1872_ = lean_array_fget_borrowed(v_keys_1866_, v_i_1868_);
v_v_1873_ = lean_array_fget_borrowed(v_vals_1867_, v_i_1868_);
if (lean_obj_tag(v_k_1872_) == 0)
{
uint64_t v___x_1886_; 
v___x_1886_ = 1723ULL;
v___y_1875_ = v___x_1886_;
goto v___jp_1874_;
}
else
{
uint64_t v_hash_1887_; 
v_hash_1887_ = lean_ctor_get_uint64(v_k_1872_, sizeof(void*)*2);
v___y_1875_ = v_hash_1887_;
goto v___jp_1874_;
}
v___jp_1874_:
{
size_t v_h_1876_; size_t v___x_1877_; lean_object* v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; size_t v___x_1881_; size_t v_h_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_h_1876_ = lean_uint64_to_usize(v___y_1875_);
v___x_1877_ = ((size_t)5ULL);
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = ((size_t)1ULL);
v___x_1880_ = lean_usize_sub(v_depth_1865_, v___x_1879_);
v___x_1881_ = lean_usize_mul(v___x_1877_, v___x_1880_);
v_h_1882_ = lean_usize_shift_right(v_h_1876_, v___x_1881_);
v___x_1883_ = lean_nat_add(v_i_1868_, v___x_1878_);
lean_dec(v_i_1868_);
lean_inc(v_v_1873_);
lean_inc(v_k_1872_);
v___x_1884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_entries_1869_, v_h_1882_, v_depth_1865_, v_k_1872_, v_v_1873_);
v_i_1868_ = v___x_1883_;
v_entries_1869_ = v___x_1884_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1888_, lean_object* v_keys_1889_, lean_object* v_vals_1890_, lean_object* v_i_1891_, lean_object* v_entries_1892_){
_start:
{
size_t v_depth_boxed_1893_; lean_object* v_res_1894_; 
v_depth_boxed_1893_ = lean_unbox_usize(v_depth_1888_);
lean_dec(v_depth_1888_);
v_res_1894_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1893_, v_keys_1889_, v_vals_1890_, v_i_1891_, v_entries_1892_);
lean_dec_ref(v_vals_1890_);
lean_dec_ref(v_keys_1889_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg___boxed(lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
size_t v_x_516__boxed_1900_; size_t v_x_517__boxed_1901_; lean_object* v_res_1902_; 
v_x_516__boxed_1900_ = lean_unbox_usize(v_x_1896_);
lean_dec(v_x_1896_);
v_x_517__boxed_1901_ = lean_unbox_usize(v_x_1897_);
lean_dec(v_x_1897_);
v_res_1902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_x_1895_, v_x_516__boxed_1900_, v_x_517__boxed_1901_, v_x_1898_, v_x_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0___redArg(lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
uint64_t v___y_1907_; 
if (lean_obj_tag(v_x_1904_) == 0)
{
uint64_t v___x_1911_; 
v___x_1911_ = 1723ULL;
v___y_1907_ = v___x_1911_;
goto v___jp_1906_;
}
else
{
uint64_t v_hash_1912_; 
v_hash_1912_ = lean_ctor_get_uint64(v_x_1904_, sizeof(void*)*2);
v___y_1907_ = v_hash_1912_;
goto v___jp_1906_;
}
v___jp_1906_:
{
size_t v___x_1908_; size_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_uint64_to_usize(v___y_1907_);
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_x_1903_, v___x_1908_, v___x_1909_, v_x_1904_, v_x_1905_);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1(lean_object* v_as_1913_, size_t v_i_1914_, size_t v_stop_1915_, lean_object* v_b_1916_){
_start:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_usize_dec_eq(v_i_1914_, v_stop_1915_);
if (v___x_1917_ == 0)
{
size_t v___x_1918_; size_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1918_ = ((size_t)1ULL);
v___x_1919_ = lean_usize_sub(v_i_1914_, v___x_1918_);
v___x_1920_ = lean_array_uget_borrowed(v_as_1913_, v___x_1919_);
v___x_1921_ = l_Lean_IR_Decl_name(v___x_1920_);
lean_inc(v___x_1920_);
v___x_1922_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0___redArg(v_b_1916_, v___x_1921_, v___x_1920_);
v_i_1914_ = v___x_1919_;
v_b_1916_ = v___x_1922_;
goto _start;
}
else
{
return v_b_1916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1___boxed(lean_object* v_as_1924_, lean_object* v_i_1925_, lean_object* v_stop_1926_, lean_object* v_b_1927_){
_start:
{
size_t v_i_boxed_1928_; size_t v_stop_boxed_1929_; lean_object* v_res_1930_; 
v_i_boxed_1928_ = lean_unbox_usize(v_i_1925_);
lean_dec(v_i_1925_);
v_stop_boxed_1929_ = lean_unbox_usize(v_stop_1926_);
lean_dec(v_stop_1926_);
v_res_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1(v_as_1924_, v_i_boxed_1928_, v_stop_boxed_1929_, v_b_1927_);
lean_dec_ref(v_as_1924_);
return v_res_1930_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(lean_object* v_decls_1933_){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1934_ = lean_obj_once(&l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0, &l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0_once, _init_l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___closed__0);
v___x_1935_ = lean_array_get_size(v_decls_1933_);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_nat_dec_lt(v___x_1936_, v___x_1935_);
if (v___x_1937_ == 0)
{
return v___x_1934_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_usize_of_nat(v___x_1935_);
v___x_1939_ = ((size_t)0ULL);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__1(v_decls_1933_, v___x_1938_, v___x_1939_, v___x_1934_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap___boxed(lean_object* v_decls_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(v_decls_1941_);
lean_dec_ref(v_decls_1941_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0(lean_object* v_00_u03b2_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0___redArg(v_x_1944_, v_x_1945_, v_x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0(lean_object* v_00_u03b2_1948_, lean_object* v_x_1949_, size_t v_x_1950_, size_t v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___redArg(v_x_1949_, v_x_1950_, v_x_1951_, v_x_1952_, v_x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_){
_start:
{
size_t v_x_731__boxed_1961_; size_t v_x_732__boxed_1962_; lean_object* v_res_1963_; 
v_x_731__boxed_1961_ = lean_unbox_usize(v_x_1957_);
lean_dec(v_x_1957_);
v_x_732__boxed_1962_ = lean_unbox_usize(v_x_1958_);
lean_dec(v_x_1958_);
v_res_1963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0(v_00_u03b2_1955_, v_x_1956_, v_x_731__boxed_1961_, v_x_732__boxed_1962_, v_x_1959_, v_x_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1964_, lean_object* v_n_1965_, lean_object* v_k_1966_, lean_object* v_v_1967_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1___redArg(v_n_1965_, v_k_1966_, v_v_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1969_, size_t v_depth_1970_, lean_object* v_keys_1971_, lean_object* v_vals_1972_, lean_object* v_heq_1973_, lean_object* v_i_1974_, lean_object* v_entries_1975_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___redArg(v_depth_1970_, v_keys_1971_, v_vals_1972_, v_i_1974_, v_entries_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1977_, lean_object* v_depth_1978_, lean_object* v_keys_1979_, lean_object* v_vals_1980_, lean_object* v_heq_1981_, lean_object* v_i_1982_, lean_object* v_entries_1983_){
_start:
{
size_t v_depth_boxed_1984_; lean_object* v_res_1985_; 
v_depth_boxed_1984_ = lean_unbox_usize(v_depth_1978_);
lean_dec(v_depth_1978_);
v_res_1985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__2(v_00_u03b2_1977_, v_depth_boxed_1984_, v_keys_1979_, v_vals_1980_, v_heq_1981_, v_i_1982_, v_entries_1983_);
lean_dec_ref(v_vals_1980_);
lean_dec_ref(v_keys_1979_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1987_, v_x_1988_, v_x_1989_, v_x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(lean_object* v_decls_1996_, lean_object* v_decl_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__0));
lean_inc_ref(v_decl_1997_);
v___x_2002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v_decl_1997_);
lean_ctor_set(v___x_2002_, 2, v_decls_1996_);
v___x_2003_ = ((lean_object*)(l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___closed__1));
v___x_2004_ = lean_st_mk_ref(v___x_2003_);
v___x_2005_ = l_Lean_IR_Checker_checkDecl(v_decl_1997_, v___x_2002_, v___x_2004_, v_a_1998_, v_a_1999_);
lean_dec_ref_known(v___x_2002_, 3);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2014_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2014_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2014_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_st_ref_get(v___x_2004_);
lean_dec(v___x_2004_);
lean_dec(v___x_2010_);
if (v_isShared_2009_ == 0)
{
v___x_2012_ = v___x_2008_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2006_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_dec(v___x_2004_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap___boxed(lean_object* v_decls_2015_, lean_object* v_decl_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(v_decls_2015_, v_decl_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_2021_, lean_object* v_decl_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(v_decls_2021_);
v___x_2027_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(v___x_2026_, v_decl_2022_, v_a_2023_, v_a_2024_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* v_decls_2028_, lean_object* v_decl_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_IR_checkDecl(v_decls_2028_, v_decl_2029_, v_a_2030_, v_a_2031_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec_ref(v_decls_2028_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* v_declMap_2034_, lean_object* v_as_2035_, size_t v_i_2036_, size_t v_stop_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v___x_2042_; 
v___x_2042_ = lean_usize_dec_eq(v_i_2036_, v_stop_2037_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_array_uget_borrowed(v_as_2035_, v_i_2036_);
lean_inc(v___x_2043_);
lean_inc_ref(v_declMap_2034_);
v___x_2044_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_checkDeclWithMap(v_declMap_2034_, v___x_2043_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; size_t v___x_2046_; size_t v___x_2047_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2036_, v___x_2046_);
v_i_2036_ = v___x_2047_;
v_b_2038_ = v_a_2045_;
goto _start;
}
else
{
lean_dec_ref(v_declMap_2034_);
return v___x_2044_;
}
}
else
{
lean_object* v___x_2049_; 
lean_dec_ref(v_declMap_2034_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_b_2038_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* v_declMap_2050_, lean_object* v_as_2051_, lean_object* v_i_2052_, lean_object* v_stop_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
size_t v_i_boxed_2058_; size_t v_stop_boxed_2059_; lean_object* v_res_2060_; 
v_i_boxed_2058_ = lean_unbox_usize(v_i_2052_);
lean_dec(v_i_2052_);
v_stop_boxed_2059_ = lean_unbox_usize(v_stop_2053_);
lean_dec(v_stop_2053_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_declMap_2050_, v_as_2051_, v_i_boxed_2058_, v_stop_boxed_2059_, v_b_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec_ref(v_as_2051_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* v_decls_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = lean_array_get_size(v_decls_2061_);
v___x_2067_ = lean_box(0);
v___x_2068_ = lean_nat_dec_lt(v___x_2065_, v___x_2066_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
return v___x_2069_;
}
else
{
lean_object* v_declMap_2070_; size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v_declMap_2070_ = l___private_Lean_Compiler_IR_Checker_0__Lean_IR_mkDeclMap(v_decls_2061_);
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = lean_usize_of_nat(v___x_2066_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_declMap_2070_, v_decls_2061_, v___x_2071_, v___x_2072_, v___x_2067_, v_a_2062_, v_a_2063_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_IR_checkDecls(v_decls_2074_, v_a_2075_, v_a_2076_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_decls_2074_);
return v_res_2078_;
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
