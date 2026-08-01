// Lean compiler output
// Module: Lean.Compiler.LCNF.Check
// Imports: public import Lean.Compiler.LCNF.PrettyPrinter public import Lean.Compiler.LCNF.CompatibleTypes public import Lean.Compiler.InductiveOverride
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
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(uint8_t, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Compiler_hasInductiveOverride(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInductiveOverride_x3f(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(uint8_t, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "invalid out of scope free variable "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "type mismatch at LCNF application"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nargument "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " has type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "\nbut is expected to have type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "invalid jump to out of scope join point `"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "LCNF parameter mismatch at `"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "`, does not value in local context"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "LCNF let declaration mismatch at `"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "`, does not match value in local context"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "type mismatch at `"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`, value has type"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "invalid LCNF, free variables are not unique `"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withJp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withJp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value),((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value),((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value),((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value),((lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LCNF check"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_check___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "LCNF local function declaration mismatch at `"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`, declaration in local context does match"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "`, type in local context"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nexpected"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`, binder name in local context `"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_check___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid LCNF `goto`, join point "};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_check___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_check___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_check___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " has #"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_check___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_check___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__4;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_check___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " parameters, but #"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_check___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_check___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__6;
static const lean_string_object l_Lean_Compiler_LCNF_Check_Pure_check___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " were provided"};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_check___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_check___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid LCNF `cases`, `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "` has # "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " fields, but alternative has # "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " alternatives"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` is not a constructor of `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` is not a constructor name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "invalid LCNF `cases`, alternative `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` occurs more than once"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__14_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__15;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_1_);
if (lean_obj_tag(v___x_3_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_13_; 
v_a_4_ = lean_ctor_get(v___x_3_, 0);
v_isSharedCheck_13_ = !lean_is_exclusive(v___x_3_);
if (v_isSharedCheck_13_ == 0)
{
v___x_6_ = v___x_3_;
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_a_4_);
lean_dec(v___x_3_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v_checkTypes_8_; lean_object* v___x_9_; lean_object* v___x_11_; 
v_checkTypes_8_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*4);
lean_dec(v_a_4_);
v___x_9_ = lean_box(v_checkTypes_8_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 0, v___x_9_);
v___x_11_ = v___x_6_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
else
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_a_14_ = lean_ctor_get(v___x_3_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_3_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v___x_3_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_3_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg___boxed(lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_22_);
lean_dec_ref(v_a_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkTypes(lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_28_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkTypes___boxed(lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes(v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_42_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_43_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0);
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
lean_ctor_set(v___x_48_, 2, v___x_47_);
lean_ctor_set(v___x_48_, 3, v___x_47_);
lean_ctor_set(v___x_48_, 4, v___x_46_);
lean_ctor_set(v___x_48_, 5, v___x_46_);
lean_ctor_set(v___x_48_, 6, v___x_46_);
lean_ctor_set(v___x_48_, 7, v___x_46_);
lean_ctor_set(v___x_48_, 8, v___x_46_);
lean_ctor_set(v___x_48_, 9, v___x_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(lean_object* v_msg_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_options_55_; lean_object* v_ref_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_options_55_ = lean_ctor_get(v___y_52_, 2);
v_ref_56_ = lean_ctor_get(v___y_52_, 5);
v___x_57_ = lean_st_ref_get(v___y_53_);
v___x_58_ = lean_st_ref_get(v___y_51_);
v___x_59_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_50_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_82_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_82_ == 0)
{
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_82_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_82_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_env_64_; lean_object* v_lctx_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_80_; 
v_env_64_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_env_64_);
lean_dec(v___x_57_);
v_lctx_65_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_58_, 1);
lean_dec(v_unused_81_);
v___x_67_ = v___x_58_;
v_isShared_68_ = v_isSharedCheck_80_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_lctx_65_);
lean_dec(v___x_58_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_80_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_69_ = lean_unbox(v_a_60_);
lean_dec(v_a_60_);
v___x_70_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_65_, v___x_69_);
lean_dec_ref(v_lctx_65_);
v___x_71_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
lean_inc_ref(v_options_55_);
v___x_72_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_72_, 0, v_env_64_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_ctor_set(v___x_72_, 2, v___x_70_);
lean_ctor_set(v___x_72_, 3, v_options_55_);
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 3);
lean_ctor_set(v___x_67_, 1, v_msg_49_);
lean_ctor_set(v___x_67_, 0, v___x_72_);
v___x_74_ = v___x_67_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_msg_49_);
v___x_74_ = v_reuseFailAlloc_79_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
lean_inc(v_ref_56_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_ref_56_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
if (v_isShared_63_ == 0)
{
lean_ctor_set_tag(v___x_62_, 1);
lean_ctor_set(v___x_62_, 0, v___x_75_);
v___x_77_ = v___x_62_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_dec(v___x_58_);
lean_dec(v___x_57_);
lean_dec_ref(v_msg_49_);
v_a_83_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_59_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_59_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___boxed(lean_object* v_msg_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v_msg_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1(lean_object* v_00_u03b1_98_, lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v_msg_99_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___boxed(lean_object* v_00_u03b1_109_, lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1(v_00_u03b1_109_, v_msg_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_119_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(lean_object* v_k_120_, lean_object* v_t_121_){
_start:
{
if (lean_obj_tag(v_t_121_) == 0)
{
lean_object* v_k_122_; lean_object* v_l_123_; lean_object* v_r_124_; uint8_t v___x_125_; 
v_k_122_ = lean_ctor_get(v_t_121_, 1);
v_l_123_ = lean_ctor_get(v_t_121_, 3);
v_r_124_ = lean_ctor_get(v_t_121_, 4);
v___x_125_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_120_, v_k_122_);
switch(v___x_125_)
{
case 0:
{
v_t_121_ = v_l_123_;
goto _start;
}
case 1:
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
default: 
{
v_t_121_ = v_r_124_;
goto _start;
}
}
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg___boxed(lean_object* v_k_130_, lean_object* v_t_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_k_130_, v_t_131_);
lean_dec(v_t_131_);
lean_dec(v_k_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0));
v___x_136_ = l_Lean_stringToMessageData(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFVar(lean_object* v_fvarId_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_vars_146_; uint8_t v___x_147_; 
v_vars_146_ = lean_ctor_get(v_a_138_, 1);
v___x_147_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_fvarId_137_, v_vars_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_137_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1);
v___x_151_ = l_Lean_MessageData_ofName(v_a_149_);
v___x_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_152_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
return v___x_153_;
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_148_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_148_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_fvarId_137_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFVar___boxed(lean_object* v_fvarId_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(v_fvarId_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_173_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(lean_object* v_00_u03b2_174_, lean_object* v_k_175_, lean_object* v_t_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_k_175_, v_t_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___boxed(lean_object* v_00_u03b2_178_, lean_object* v_k_179_, lean_object* v_t_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(v_00_u03b2_178_, v_k_179_, v_t_180_);
lean_dec(v_t_180_);
lean_dec(v_k_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___redArg(lean_object* v_f_183_, lean_object* v_i_184_, lean_object* v_a_185_){
_start:
{
if (lean_obj_tag(v_f_183_) == 4)
{
lean_object* v_declName_187_; lean_object* v___x_188_; lean_object* v_numParams_190_; lean_object* v_env_198_; lean_object* v___x_207_; 
v_declName_187_ = lean_ctor_get(v_f_183_, 0);
lean_inc_n(v_declName_187_, 2);
lean_dec_ref_known(v_f_183_, 2);
v___x_188_ = lean_st_ref_get(v_a_185_);
v_env_198_ = lean_ctor_get(v___x_188_, 0);
lean_inc_ref_n(v_env_198_, 2);
lean_dec(v___x_188_);
v___x_207_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_198_, v_declName_187_);
if (lean_obj_tag(v___x_207_) == 1)
{
lean_object* v_val_208_; 
v_val_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_207_, 1);
if (lean_obj_tag(v_val_208_) == 2)
{
lean_object* v_info_209_; lean_object* v_numParams_210_; 
lean_dec_ref(v_env_198_);
lean_dec(v_declName_187_);
v_info_209_ = lean_ctor_get(v_val_208_, 1);
lean_inc_ref(v_info_209_);
lean_dec_ref_known(v_val_208_, 2);
v_numParams_210_ = lean_ctor_get(v_info_209_, 2);
lean_inc(v_numParams_210_);
lean_dec_ref(v_info_209_);
v_numParams_190_ = v_numParams_210_;
goto v___jp_189_;
}
else
{
lean_dec(v_val_208_);
goto v___jp_199_;
}
}
else
{
lean_dec(v___x_207_);
goto v___jp_199_;
}
v___jp_189_:
{
uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_nat_dec_lt(v_i_184_, v_numParams_190_);
lean_dec(v_numParams_190_);
v___x_192_ = lean_box(v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
v___jp_194_:
{
uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = 0;
v___x_196_ = lean_box(v___x_195_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
v___jp_199_:
{
uint8_t v___x_200_; lean_object* v___x_201_; 
v___x_200_ = 0;
lean_inc_ref(v_env_198_);
v___x_201_ = l_Lean_Environment_find_x3f(v_env_198_, v_declName_187_, v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_dec_ref(v_env_198_);
goto v___jp_194_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_201_, 1);
if (lean_obj_tag(v_val_202_) == 6)
{
lean_object* v_val_203_; lean_object* v_induct_204_; lean_object* v_numParams_205_; uint8_t v___x_206_; 
v_val_203_ = lean_ctor_get(v_val_202_, 0);
lean_inc_ref(v_val_203_);
lean_dec_ref_known(v_val_202_, 1);
v_induct_204_ = lean_ctor_get(v_val_203_, 1);
lean_inc(v_induct_204_);
v_numParams_205_ = lean_ctor_get(v_val_203_, 3);
lean_inc(v_numParams_205_);
lean_dec_ref(v_val_203_);
v___x_206_ = l_Lean_Compiler_hasInductiveOverride(v_env_198_, v_induct_204_);
if (v___x_206_ == 0)
{
v_numParams_190_ = v_numParams_205_;
goto v___jp_189_;
}
else
{
lean_dec(v_numParams_205_);
goto v___jp_194_;
}
}
else
{
lean_dec(v_val_202_);
lean_dec_ref(v_env_198_);
goto v___jp_194_;
}
}
}
}
else
{
uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref(v_f_183_);
v___x_211_ = 0;
v___x_212_ = lean_box(v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___redArg___boxed(lean_object* v_f_214_, lean_object* v_i_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___redArg(v_f_214_, v_i_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec(v_i_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(lean_object* v_f_219_, lean_object* v_i_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___redArg(v_f_219_, v_i_220_, v_a_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___boxed(lean_object* v_f_225_, lean_object* v_i_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(v_f_225_, v_i_226_, v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_i_226_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(size_t v_sz_231_, size_t v_i_232_, lean_object* v_bs_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_lt(v_i_232_, v_sz_231_);
if (v___x_234_ == 0)
{
return v_bs_233_;
}
else
{
lean_object* v_v_235_; lean_object* v___x_236_; lean_object* v_bs_x27_237_; lean_object* v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v_v_235_ = lean_array_uget(v_bs_233_, v_i_232_);
v___x_236_ = lean_unsigned_to_nat(0u);
v_bs_x27_237_ = lean_array_uset(v_bs_233_, v_i_232_, v___x_236_);
v___x_238_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v_v_235_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_232_, v___x_239_);
v___x_241_ = lean_array_uset(v_bs_x27_237_, v_i_232_, v___x_238_);
v_i_232_ = v___x_240_;
v_bs_233_ = v___x_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0___boxed(lean_object* v_sz_243_, lean_object* v_i_244_, lean_object* v_bs_245_){
_start:
{
size_t v_sz_boxed_246_; size_t v_i_boxed_247_; lean_object* v_res_248_; 
v_sz_boxed_246_ = lean_unbox_usize(v_sz_243_);
lean_dec(v_sz_243_);
v_i_boxed_247_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(v_sz_boxed_246_, v_i_boxed_247_, v_bs_245_);
return v_res_248_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2));
v___x_254_ = l_Lean_stringToMessageData(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6));
v___x_260_ = l_Lean_stringToMessageData(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(lean_object* v___x_261_, lean_object* v___x_262_, lean_object* v_a_263_, lean_object* v_args_264_, lean_object* v_f_265_, lean_object* v_____x_266_, lean_object* v_fType_267_, lean_object* v_j_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_352_; 
v_fst_277_ = lean_ctor_get(v_____x_266_, 0);
v_snd_278_ = lean_ctor_get(v_____x_266_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_____x_266_);
if (v_isSharedCheck_352_ == 0)
{
v___x_280_ = v_____x_266_;
v_isShared_281_ = v_isSharedCheck_352_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_snd_278_);
lean_inc(v_fst_277_);
lean_dec(v_____x_266_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_352_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v___y_272_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; uint8_t v___x_291_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v___x_289_, 1);
v___x_291_ = lean_unbox(v_a_290_);
lean_dec(v_a_290_);
if (v___x_291_ == 0)
{
lean_dec(v_fst_277_);
lean_dec_ref(v_f_265_);
lean_dec_ref(v_args_264_);
lean_dec(v___x_262_);
goto v___jp_282_;
}
else
{
uint8_t v___x_292_; lean_object* v___x_293_; 
v___x_292_ = 0;
lean_inc(v___x_262_);
v___x_293_ = l_Lean_Compiler_LCNF_Arg_inferType(v___x_292_, v___x_262_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_n(v_a_294_, 2);
lean_dec_ref_known(v___x_293_, 1);
lean_inc_ref(v_args_264_);
v___x_295_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v_fst_277_, v_j_268_, v_a_263_, v_args_264_);
lean_dec(v_fst_277_);
lean_inc_ref(v___x_295_);
v___x_296_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_a_294_, v___x_295_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
v___x_298_ = lean_unbox(v_a_297_);
lean_dec(v_a_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; size_t v_sz_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_299_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1);
v_sz_300_ = lean_array_size(v_args_264_);
v___x_301_ = ((size_t)0ULL);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(v_sz_300_, v___x_301_, v_args_264_);
v___x_303_ = l_Lean_mkAppN(v_f_265_, v___x_302_);
lean_dec_ref(v___x_302_);
v___x_304_ = l_Lean_indentExpr(v___x_303_);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_299_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v___x_262_);
v___x_309_ = l_Lean_MessageData_ofExpr(v___x_308_);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_307_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l_Lean_indentExpr(v_a_294_);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_indentExpr(v___x_295_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_318_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_dec_ref_known(v___x_319_, 1);
goto v___jp_282_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_del_object(v___x_280_);
lean_dec(v_snd_278_);
lean_dec(v_j_268_);
lean_dec(v___x_261_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_dec_ref(v___x_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_f_265_);
lean_dec_ref(v_args_264_);
lean_dec(v___x_262_);
goto v___jp_282_;
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v___x_295_);
lean_dec(v_a_294_);
lean_del_object(v___x_280_);
lean_dec(v_snd_278_);
lean_dec(v_j_268_);
lean_dec_ref(v_f_265_);
lean_dec_ref(v_args_264_);
lean_dec(v___x_262_);
lean_dec(v___x_261_);
v_a_328_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_296_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_296_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_del_object(v___x_280_);
lean_dec(v_snd_278_);
lean_dec(v_fst_277_);
lean_dec(v_j_268_);
lean_dec_ref(v_f_265_);
lean_dec_ref(v_args_264_);
lean_dec(v___x_262_);
lean_dec(v___x_261_);
v_a_336_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_293_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_293_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_del_object(v___x_280_);
lean_dec(v_snd_278_);
lean_dec(v_fst_277_);
lean_dec(v_j_268_);
lean_dec_ref(v_f_265_);
lean_dec_ref(v_args_264_);
lean_dec(v___x_262_);
lean_dec(v___x_261_);
v_a_344_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_289_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_289_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
v___jp_282_:
{
lean_object* v___x_284_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v_j_268_);
lean_ctor_set(v___x_280_, 0, v_snd_278_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_snd_278_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_j_268_);
v___x_284_ = v_reuseFailAlloc_288_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_261_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___boxed(lean_object* v___x_353_, lean_object* v___x_354_, lean_object* v_a_355_, lean_object* v_args_356_, lean_object* v_f_357_, lean_object* v_____x_358_, lean_object* v_fType_359_, lean_object* v_j_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_353_, v___x_354_, v_a_355_, v_args_356_, v_f_357_, v_____x_358_, v_fType_359_, v_j_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v_fType_359_);
lean_dec(v_a_355_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(lean_object* v_upperBound_372_, lean_object* v_args_373_, lean_object* v_f_374_, lean_object* v_a_375_, lean_object* v_b_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___y_386_; uint8_t v___x_408_; 
v___x_408_ = lean_nat_dec_lt(v_a_375_, v_upperBound_372_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec(v_a_375_);
lean_dec_ref(v_f_374_);
lean_dec_ref(v_args_373_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_b_376_);
return v___x_409_;
}
else
{
lean_object* v_snd_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_454_; 
v_snd_410_ = lean_ctor_get(v_b_376_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_b_376_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v_b_376_, 0);
lean_dec(v_unused_455_);
v___x_412_ = v_b_376_;
v_isShared_413_ = v_isSharedCheck_454_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_snd_410_);
lean_dec(v_b_376_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_454_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_453_; 
v_fst_414_ = lean_ctor_get(v_snd_410_, 0);
v_snd_415_ = lean_ctor_get(v_snd_410_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_snd_410_);
if (v_isSharedCheck_453_ == 0)
{
v___x_417_ = v_snd_410_;
v_isShared_418_ = v_isSharedCheck_453_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_snd_415_);
lean_inc(v_fst_414_);
lean_dec(v_snd_410_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_453_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
uint8_t v___x_419_; 
v___x_419_ = l_Lean_Expr_isErased(v_fst_414_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_box(0);
v___x_421_ = lean_array_fget_borrowed(v_args_373_, v_a_375_);
v___x_422_ = l_Lean_Expr_headBeta(v_fst_414_);
if (lean_obj_tag(v___x_422_) == 7)
{
lean_object* v_binderType_423_; lean_object* v_body_424_; lean_object* v___x_426_; 
lean_del_object(v___x_412_);
v_binderType_423_ = lean_ctor_get(v___x_422_, 1);
lean_inc_ref(v_binderType_423_);
v_body_424_ = lean_ctor_get(v___x_422_, 2);
lean_inc_ref(v_body_424_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_body_424_);
lean_ctor_set(v___x_417_, 0, v_binderType_423_);
v___x_426_ = v___x_417_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_binderType_423_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_body_424_);
v___x_426_ = v_reuseFailAlloc_428_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; 
lean_inc_ref(v_f_374_);
lean_inc_ref(v_args_373_);
lean_inc(v___x_421_);
v___x_427_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_420_, v___x_421_, v_a_375_, v_args_373_, v_f_374_, v___x_426_, v___x_422_, v_snd_415_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec_ref_known(v___x_422_, 3);
v___y_386_ = v___x_427_;
goto v___jp_385_;
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_inc_ref(v_args_373_);
v___x_429_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v___x_422_, v_snd_415_, v_a_375_, v_args_373_);
lean_dec_ref(v___x_422_);
v___x_430_ = l_Lean_Expr_headBeta(v___x_429_);
if (lean_obj_tag(v___x_430_) == 7)
{
lean_object* v_binderType_431_; lean_object* v_body_432_; lean_object* v___x_434_; 
lean_dec(v_snd_415_);
lean_del_object(v___x_412_);
v_binderType_431_ = lean_ctor_get(v___x_430_, 1);
lean_inc_ref(v_binderType_431_);
v_body_432_ = lean_ctor_get(v___x_430_, 2);
lean_inc_ref(v_body_432_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_body_432_);
lean_ctor_set(v___x_417_, 0, v_binderType_431_);
v___x_434_ = v___x_417_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_binderType_431_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_body_432_);
v___x_434_ = v_reuseFailAlloc_436_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; 
lean_inc_ref(v_f_374_);
lean_inc_ref(v_args_373_);
lean_inc(v_a_375_);
lean_inc(v___x_421_);
v___x_435_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_420_, v___x_421_, v_a_375_, v_args_373_, v_f_374_, v___x_434_, v___x_430_, v_a_375_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec_ref_known(v___x_430_, 3);
v___y_386_ = v___x_435_;
goto v___jp_385_;
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_439_; 
lean_dec(v_a_375_);
lean_dec_ref(v_f_374_);
lean_dec_ref(v_args_373_);
v___x_437_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0));
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_430_);
v___x_439_ = v___x_417_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_snd_415_);
v___x_439_ = v_reuseFailAlloc_444_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_439_);
lean_ctor_set(v___x_412_, 0, v___x_437_);
v___x_441_ = v___x_412_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_439_);
v___x_441_ = v_reuseFailAlloc_443_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_447_; 
lean_dec(v_a_375_);
lean_dec_ref(v_f_374_);
lean_dec_ref(v_args_373_);
v___x_445_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0));
if (v_isShared_418_ == 0)
{
v___x_447_ = v___x_417_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_fst_414_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_snd_415_);
v___x_447_ = v_reuseFailAlloc_452_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_447_);
lean_ctor_set(v___x_412_, 0, v___x_445_);
v___x_449_ = v___x_412_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_451_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
}
}
}
}
v___jp_385_:
{
if (lean_obj_tag(v___y_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_399_; 
v_a_387_ = lean_ctor_get(v___y_386_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___y_386_);
if (v_isSharedCheck_399_ == 0)
{
v___x_389_ = v___y_386_;
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___y_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
if (lean_obj_tag(v_a_387_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; 
lean_dec(v_a_375_);
lean_dec_ref(v_f_374_);
lean_dec_ref(v_args_373_);
v_a_391_ = lean_ctor_get(v_a_387_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v_a_387_, 1);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_a_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_del_object(v___x_389_);
v_a_395_ = lean_ctor_get(v_a_387_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v_a_387_, 1);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_a_375_, v___x_396_);
lean_dec(v_a_375_);
v_a_375_ = v___x_397_;
v_b_376_ = v_a_395_;
goto _start;
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_a_375_);
lean_dec_ref(v_f_374_);
lean_dec_ref(v_args_373_);
v_a_400_ = lean_ctor_get(v___y_386_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___y_386_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___y_386_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___y_386_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___boxed(lean_object* v_upperBound_456_, lean_object* v_args_457_, lean_object* v_f_458_, lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v_upperBound_456_, v_args_457_, v_f_458_, v_a_459_, v_b_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v_upperBound_456_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(lean_object* v_f_470_, lean_object* v_args_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; 
lean_inc_ref(v_f_470_);
v___x_480_ = l_Lean_Compiler_LCNF_inferType(v_f_470_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = lean_array_get_size(v_args_471_);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_box(0);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_a_481_);
lean_ctor_set(v___x_485_, 1, v___x_483_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v___x_482_, v_args_471_, v_f_470_, v___x_483_, v___x_486_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_501_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_501_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_501_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_501_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_fst_492_; 
v_fst_492_ = lean_ctor_get(v_a_488_, 0);
lean_inc(v_fst_492_);
lean_dec(v_a_488_);
if (lean_obj_tag(v_fst_492_) == 0)
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_box(0);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_493_);
v___x_495_ = v___x_490_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v_val_497_; lean_object* v___x_499_; 
v_val_497_ = lean_ctor_get(v_fst_492_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_fst_492_, 1);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_val_497_);
v___x_499_ = v___x_490_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_val_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_502_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_487_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_487_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_args_471_);
lean_dec_ref(v_f_470_);
v_a_510_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_480_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_480_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs___boxed(lean_object* v_f_518_, lean_object* v_args_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(v_f_518_, v_args_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1(lean_object* v_upperBound_529_, lean_object* v_args_530_, lean_object* v_f_531_, lean_object* v_inst_532_, lean_object* v_R_533_, lean_object* v_a_534_, lean_object* v_b_535_, lean_object* v_c_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v_upperBound_529_, v_args_530_, v_f_531_, v_a_534_, v_b_535_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___boxed(lean_object* v_upperBound_546_, lean_object* v_args_547_, lean_object* v_f_548_, lean_object* v_inst_549_, lean_object* v_R_550_, lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v_c_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1(v_upperBound_546_, v_args_547_, v_f_548_, v_inst_549_, v_R_550_, v_a_551_, v_b_552_, v_c_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v_upperBound_546_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(lean_object* v_e_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
switch(lean_obj_tag(v_e_563_))
{
case 0:
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v_isSharedCheck_579_ = !lean_is_exclusive(v_e_563_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v_e_563_, 0);
lean_dec(v_unused_580_);
v___x_573_ = v_e_563_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_e_563_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
case 1:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_box(0);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
case 2:
{
lean_object* v_struct_583_; lean_object* v___x_584_; 
v_struct_583_ = lean_ctor_get(v_e_563_, 2);
lean_inc(v_struct_583_);
lean_dec_ref_known(v_e_563_, 3);
v___x_584_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(v_struct_583_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
return v___x_584_;
}
case 3:
{
lean_object* v_declName_585_; lean_object* v_us_586_; lean_object* v_args_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_declName_585_ = lean_ctor_get(v_e_563_, 0);
lean_inc(v_declName_585_);
v_us_586_ = lean_ctor_get(v_e_563_, 1);
lean_inc(v_us_586_);
v_args_587_ = lean_ctor_get(v_e_563_, 2);
lean_inc_ref(v_args_587_);
lean_dec_ref_known(v_e_563_, 3);
v___x_588_ = l_Lean_mkConst(v_declName_585_, v_us_586_);
v___x_589_ = l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(v___x_588_, v_args_587_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
return v___x_589_;
}
default: 
{
lean_object* v_fvarId_590_; lean_object* v_args_591_; lean_object* v___x_592_; 
v_fvarId_590_ = lean_ctor_get(v_e_563_, 0);
lean_inc_n(v_fvarId_590_, 2);
v_args_591_ = lean_ctor_get(v_e_563_, 1);
lean_inc_ref(v_args_591_);
lean_dec_ref_known(v_e_563_, 2);
v___x_592_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(v_fvarId_590_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec_ref_known(v___x_592_, 1);
v___x_593_ = l_Lean_Expr_fvar___override(v_fvarId_590_);
v___x_594_ = l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(v___x_593_, v_args_591_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
return v___x_594_;
}
else
{
lean_dec_ref(v_args_591_);
lean_dec(v_fvarId_590_);
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetValue___boxed(lean_object* v_e_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(v_e_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
return v_res_604_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0));
v___x_607_ = l_Lean_stringToMessageData(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__2));
v___x_610_ = l_Lean_stringToMessageData(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(lean_object* v_jp_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_jps_618_; uint8_t v___x_619_; 
v_jps_618_ = lean_ctor_get(v_a_612_, 0);
v___x_619_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_jp_611_, v_jps_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_620_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1);
v___x_621_ = l_Lean_mkFVar(v_jp_611_);
v___x_622_ = l_Lean_MessageData_ofExpr(v___x_621_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_620_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3, &l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_625_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v_jp_611_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___boxed(lean_object* v_jp_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(v_jp_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec_ref(v_a_630_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(lean_object* v_jp_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(v_jp_637_, v_a_638_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___boxed(lean_object* v_jp_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(v_jp_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
return v_res_656_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(lean_object* v_param_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_fvarId_669_; lean_object* v_binderName_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v_fvarId_669_ = lean_ctor_get(v_param_663_, 0);
v_binderName_670_ = lean_ctor_get(v_param_663_, 1);
lean_inc(v_binderName_670_);
v___x_671_ = 0;
lean_inc(v_fvarId_669_);
v___x_672_ = l_Lean_Compiler_LCNF_getParam(v___x_671_, v_fvarId_669_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_688_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_688_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_688_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_688_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
uint8_t v___x_677_; 
v___x_677_ = l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(v_param_663_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_param_663_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_del_object(v___x_675_);
v___x_678_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1);
v___x_679_ = l_Lean_MessageData_ofName(v_binderName_670_);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3, &l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_682_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_686_; 
lean_dec(v_binderName_670_);
v___x_684_ = lean_box(0);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_684_);
v___x_686_ = v___x_675_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_binderName_670_);
lean_dec_ref(v_param_663_);
v_a_689_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_672_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_672_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___boxed(lean_object* v_param_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(v_param_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam(lean_object* v_param_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(v_param_704_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParam___boxed(lean_object* v_param_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam(v_param_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(lean_object* v_as_724_, size_t v_i_725_, size_t v_stop_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = lean_usize_dec_eq(v_i_725_, v_stop_726_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_array_uget_borrowed(v_as_724_, v_i_725_);
lean_inc(v___x_734_);
v___x_735_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(v___x_734_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; size_t v___x_737_; size_t v___x_738_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_725_, v___x_737_);
v_i_725_ = v___x_738_;
v_b_727_ = v_a_736_;
goto _start;
}
else
{
return v___x_735_;
}
}
else
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_b_727_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg___boxed(lean_object* v_as_741_, lean_object* v_i_742_, lean_object* v_stop_743_, lean_object* v_b_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
size_t v_i_boxed_750_; size_t v_stop_boxed_751_; lean_object* v_res_752_; 
v_i_boxed_750_ = lean_unbox_usize(v_i_742_);
lean_dec(v_i_742_);
v_stop_boxed_751_ = lean_unbox_usize(v_stop_743_);
lean_dec(v_stop_743_);
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_as_741_, v_i_boxed_750_, v_stop_boxed_751_, v_b_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v_as_741_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParams(lean_object* v_params_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_array_get_size(v_params_753_);
v___x_764_ = lean_box(0);
v___x_765_ = lean_nat_dec_lt(v___x_762_, v___x_763_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
return v___x_766_;
}
else
{
uint8_t v___x_767_; 
v___x_767_ = lean_nat_dec_le(v___x_763_, v___x_763_);
if (v___x_767_ == 0)
{
if (v___x_765_ == 0)
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_764_);
return v___x_768_;
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_of_nat(v___x_763_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_params_753_, v___x_769_, v___x_770_, v___x_764_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
return v___x_771_;
}
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_763_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_params_753_, v___x_772_, v___x_773_, v___x_764_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkParams___boxed(lean_object* v_params_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Compiler_LCNF_Check_Pure_checkParams(v_params_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_params_775_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(lean_object* v_as_785_, size_t v_i_786_, size_t v_stop_787_, lean_object* v_b_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_as_785_, v_i_786_, v_stop_787_, v_b_788_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___boxed(lean_object* v_as_798_, lean_object* v_i_799_, lean_object* v_stop_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
size_t v_i_boxed_810_; size_t v_stop_boxed_811_; lean_object* v_res_812_; 
v_i_boxed_810_ = lean_unbox_usize(v_i_799_);
lean_dec(v_i_799_);
v_stop_boxed_811_ = lean_unbox_usize(v_stop_800_);
lean_dec(v_stop_800_);
v_res_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(v_as_798_, v_i_boxed_810_, v_stop_boxed_811_, v_b_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_as_798_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2));
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4));
v___x_821_ = l_Lean_stringToMessageData(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6));
v___x_824_ = l_Lean_stringToMessageData(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(lean_object* v_letDecl_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_fvarId_834_; lean_object* v_binderName_835_; lean_object* v_type_836_; lean_object* v_value_837_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___x_869_; 
v_fvarId_834_ = lean_ctor_get(v_letDecl_825_, 0);
v_binderName_835_ = lean_ctor_get(v_letDecl_825_, 1);
lean_inc(v_binderName_835_);
v_type_836_ = lean_ctor_get(v_letDecl_825_, 2);
v_value_837_ = lean_ctor_get(v_letDecl_825_, 3);
lean_inc(v_value_837_);
v___x_869_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(v_value_837_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_870_; 
lean_dec_ref_known(v___x_869_, 1);
v___x_870_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_829_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; uint8_t v___x_872_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = lean_unbox(v_a_871_);
lean_dec(v_a_871_);
if (v___x_872_ == 0)
{
v___y_839_ = v_a_829_;
v___y_840_ = v_a_830_;
v___y_841_ = v_a_831_;
v___y_842_ = v_a_832_;
goto v___jp_838_;
}
else
{
uint8_t v___x_873_; lean_object* v___x_874_; 
v___x_873_ = 0;
lean_inc(v_value_837_);
v___x_874_ = l_Lean_Compiler_LCNF_LetValue_inferType(v___x_873_, v_value_837_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc_n(v_a_875_, 2);
lean_dec_ref_known(v___x_874_, 1);
lean_inc_ref(v_type_836_);
v___x_876_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_type_836_, v_a_875_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; uint8_t v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = lean_unbox(v_a_877_);
lean_dec(v_a_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_inc_ref(v_type_836_);
lean_dec_ref(v_letDecl_825_);
v___x_879_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5, &l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5);
v___x_880_ = l_Lean_MessageData_ofName(v_binderName_835_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7, &l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_indentExpr(v_a_875_);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_indentExpr(v_type_836_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_889_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
return v___x_890_;
}
else
{
lean_dec(v_a_875_);
v___y_839_ = v_a_829_;
v___y_840_ = v_a_830_;
v___y_841_ = v_a_831_;
v___y_842_ = v_a_832_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v_a_875_);
lean_dec(v_binderName_835_);
lean_dec_ref(v_letDecl_825_);
v_a_891_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_876_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_876_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
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
lean_dec(v_binderName_835_);
lean_dec_ref(v_letDecl_825_);
v_a_899_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_874_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_874_);
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
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_binderName_835_);
lean_dec_ref(v_letDecl_825_);
v_a_907_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_870_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_870_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_dec(v_binderName_835_);
lean_dec_ref(v_letDecl_825_);
return v___x_869_;
}
v___jp_838_:
{
uint8_t v___x_843_; lean_object* v___x_844_; 
v___x_843_ = 0;
lean_inc(v_fvarId_834_);
v___x_844_ = l_Lean_Compiler_LCNF_getLetDecl(v___x_843_, v_fvarId_834_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_860_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_860_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_860_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_860_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
uint8_t v___x_849_; 
v___x_849_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_843_, v_letDecl_825_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_letDecl_825_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_del_object(v___x_847_);
v___x_850_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1);
v___x_851_ = l_Lean_MessageData_ofName(v_binderName_835_);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3, &l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_854_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_858_; 
lean_dec(v_binderName_835_);
v___x_856_ = lean_box(0);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_856_);
v___x_858_ = v___x_847_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
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
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_binderName_835_);
lean_dec_ref(v_letDecl_825_);
v_a_861_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_844_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_844_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___boxed(lean_object* v_letDecl_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(v_letDecl_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
return v_res_924_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(lean_object* v_a_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
uint8_t v___x_927_; 
v___x_927_ = 0;
return v___x_927_;
}
else
{
lean_object* v_key_928_; lean_object* v_tail_929_; uint8_t v___x_930_; 
v_key_928_ = lean_ctor_get(v_x_926_, 0);
v_tail_929_ = lean_ctor_get(v_x_926_, 2);
v___x_930_ = l_Lean_instBEqFVarId_beq(v_key_928_, v_a_925_);
if (v___x_930_ == 0)
{
v_x_926_ = v_tail_929_;
goto _start;
}
else
{
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg___boxed(lean_object* v_a_932_, lean_object* v_x_933_){
_start:
{
uint8_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_932_, v_x_933_);
lean_dec(v_x_933_);
lean_dec(v_a_932_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
if (lean_obj_tag(v_x_937_) == 0)
{
return v_x_936_;
}
else
{
lean_object* v_key_938_; lean_object* v_value_939_; lean_object* v_tail_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_963_; 
v_key_938_ = lean_ctor_get(v_x_937_, 0);
v_value_939_ = lean_ctor_get(v_x_937_, 1);
v_tail_940_ = lean_ctor_get(v_x_937_, 2);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_937_);
if (v_isSharedCheck_963_ == 0)
{
v___x_942_ = v_x_937_;
v_isShared_943_ = v_isSharedCheck_963_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_tail_940_);
lean_inc(v_value_939_);
lean_inc(v_key_938_);
lean_dec(v_x_937_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_963_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; uint64_t v___x_945_; uint64_t v___x_946_; uint64_t v___x_947_; uint64_t v_fold_948_; uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; size_t v___x_952_; size_t v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_944_ = lean_array_get_size(v_x_936_);
v___x_945_ = l_Lean_instHashableFVarId_hash(v_key_938_);
v___x_946_ = 32ULL;
v___x_947_ = lean_uint64_shift_right(v___x_945_, v___x_946_);
v_fold_948_ = lean_uint64_xor(v___x_945_, v___x_947_);
v___x_949_ = 16ULL;
v___x_950_ = lean_uint64_shift_right(v_fold_948_, v___x_949_);
v___x_951_ = lean_uint64_xor(v_fold_948_, v___x_950_);
v___x_952_ = lean_uint64_to_usize(v___x_951_);
v___x_953_ = lean_usize_of_nat(v___x_944_);
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_sub(v___x_953_, v___x_954_);
v___x_956_ = lean_usize_land(v___x_952_, v___x_955_);
v___x_957_ = lean_array_uget_borrowed(v_x_936_, v___x_956_);
lean_inc(v___x_957_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 2, v___x_957_);
v___x_959_ = v___x_942_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_key_938_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_value_939_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v___x_957_);
v___x_959_ = v_reuseFailAlloc_962_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; 
v___x_960_ = lean_array_uset(v_x_936_, v___x_956_, v___x_959_);
v_x_936_ = v___x_960_;
v_x_937_ = v_tail_940_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(lean_object* v_i_964_, lean_object* v_source_965_, lean_object* v_target_966_){
_start:
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_array_get_size(v_source_965_);
v___x_968_ = lean_nat_dec_lt(v_i_964_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec_ref(v_source_965_);
lean_dec(v_i_964_);
return v_target_966_;
}
else
{
lean_object* v_es_969_; lean_object* v___x_970_; lean_object* v_source_971_; lean_object* v_target_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_es_969_ = lean_array_fget(v_source_965_, v_i_964_);
v___x_970_ = lean_box(0);
v_source_971_ = lean_array_fset(v_source_965_, v_i_964_, v___x_970_);
v_target_972_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(v_target_966_, v_es_969_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_add(v_i_964_, v___x_973_);
lean_dec(v_i_964_);
v_i_964_ = v___x_974_;
v_source_965_ = v_source_971_;
v_target_966_ = v_target_972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(lean_object* v_data_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v_nbuckets_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_977_ = lean_array_get_size(v_data_976_);
v___x_978_ = lean_unsigned_to_nat(2u);
v_nbuckets_979_ = lean_nat_mul(v___x_977_, v___x_978_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_box(0);
v___x_982_ = lean_mk_array(v_nbuckets_979_, v___x_981_);
v___x_983_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(v___x_980_, v_data_976_, v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(lean_object* v_m_984_, lean_object* v_a_985_, lean_object* v_b_986_){
_start:
{
lean_object* v_size_987_; lean_object* v_buckets_988_; lean_object* v___x_989_; uint64_t v___x_990_; uint64_t v___x_991_; uint64_t v___x_992_; uint64_t v_fold_993_; uint64_t v___x_994_; uint64_t v___x_995_; uint64_t v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; lean_object* v_bkt_1002_; uint8_t v___x_1003_; 
v_size_987_ = lean_ctor_get(v_m_984_, 0);
v_buckets_988_ = lean_ctor_get(v_m_984_, 1);
v___x_989_ = lean_array_get_size(v_buckets_988_);
v___x_990_ = l_Lean_instHashableFVarId_hash(v_a_985_);
v___x_991_ = 32ULL;
v___x_992_ = lean_uint64_shift_right(v___x_990_, v___x_991_);
v_fold_993_ = lean_uint64_xor(v___x_990_, v___x_992_);
v___x_994_ = 16ULL;
v___x_995_ = lean_uint64_shift_right(v_fold_993_, v___x_994_);
v___x_996_ = lean_uint64_xor(v_fold_993_, v___x_995_);
v___x_997_ = lean_uint64_to_usize(v___x_996_);
v___x_998_ = lean_usize_of_nat(v___x_989_);
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_sub(v___x_998_, v___x_999_);
v___x_1001_ = lean_usize_land(v___x_997_, v___x_1000_);
v_bkt_1002_ = lean_array_uget_borrowed(v_buckets_988_, v___x_1001_);
v___x_1003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_985_, v_bkt_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1024_; 
lean_inc_ref(v_buckets_988_);
lean_inc(v_size_987_);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_m_984_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1025_ = lean_ctor_get(v_m_984_, 1);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_m_984_, 0);
lean_dec(v_unused_1026_);
v___x_1005_ = v_m_984_;
v_isShared_1006_ = v_isSharedCheck_1024_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_m_984_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1024_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v_size_x27_1008_; lean_object* v___x_1009_; lean_object* v_buckets_x27_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1007_ = lean_unsigned_to_nat(1u);
v_size_x27_1008_ = lean_nat_add(v_size_987_, v___x_1007_);
lean_dec(v_size_987_);
lean_inc(v_bkt_1002_);
v___x_1009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1009_, 0, v_a_985_);
lean_ctor_set(v___x_1009_, 1, v_b_986_);
lean_ctor_set(v___x_1009_, 2, v_bkt_1002_);
v_buckets_x27_1010_ = lean_array_uset(v_buckets_988_, v___x_1001_, v___x_1009_);
v___x_1011_ = lean_unsigned_to_nat(4u);
v___x_1012_ = lean_nat_mul(v_size_x27_1008_, v___x_1011_);
v___x_1013_ = lean_unsigned_to_nat(3u);
v___x_1014_ = lean_nat_div(v___x_1012_, v___x_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_array_get_size(v_buckets_x27_1010_);
v___x_1016_ = lean_nat_dec_le(v___x_1014_, v___x_1015_);
lean_dec(v___x_1014_);
if (v___x_1016_ == 0)
{
lean_object* v_val_1017_; lean_object* v___x_1019_; 
v_val_1017_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(v_buckets_x27_1010_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v_val_1017_);
lean_ctor_set(v___x_1005_, 0, v_size_x27_1008_);
v___x_1019_ = v___x_1005_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_size_x27_1008_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_val_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
else
{
lean_object* v___x_1022_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v_buckets_x27_1010_);
lean_ctor_set(v___x_1005_, 0, v_size_x27_1008_);
v___x_1022_ = v___x_1005_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_size_x27_1008_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_buckets_x27_1010_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_dec(v_b_986_);
lean_dec(v_a_985_);
return v_m_984_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(lean_object* v_m_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_buckets_1029_; lean_object* v___x_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v_fold_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_buckets_1029_ = lean_ctor_get(v_m_1027_, 1);
v___x_1030_ = lean_array_get_size(v_buckets_1029_);
v___x_1031_ = l_Lean_instHashableFVarId_hash(v_a_1028_);
v___x_1032_ = 32ULL;
v___x_1033_ = lean_uint64_shift_right(v___x_1031_, v___x_1032_);
v_fold_1034_ = lean_uint64_xor(v___x_1031_, v___x_1033_);
v___x_1035_ = 16ULL;
v___x_1036_ = lean_uint64_shift_right(v_fold_1034_, v___x_1035_);
v___x_1037_ = lean_uint64_xor(v_fold_1034_, v___x_1036_);
v___x_1038_ = lean_uint64_to_usize(v___x_1037_);
v___x_1039_ = lean_usize_of_nat(v___x_1030_);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_sub(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_usize_land(v___x_1038_, v___x_1041_);
v___x_1043_ = lean_array_uget_borrowed(v_buckets_1029_, v___x_1042_);
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_1028_, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg___boxed(lean_object* v_m_1045_, lean_object* v_a_1046_){
_start:
{
uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_res_1047_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v_m_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_m_1045_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(lean_object* v_fvarId_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___y_1060_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_st_ref_get(v_a_1053_);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v___x_1066_, v_fvarId_1052_);
lean_dec(v___x_1066_);
if (v___x_1067_ == 0)
{
v___y_1060_ = v_a_1053_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1068_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1);
v___x_1069_ = l_Lean_MessageData_ofName(v_fvarId_1052_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3, &l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_1072_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
return v___x_1073_;
}
v___jp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1061_ = lean_st_ref_take(v___y_1060_);
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(v___x_1061_, v_fvarId_1052_, v___x_1062_);
v___x_1064_ = lean_st_ref_set(v___y_1060_, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___boxed(lean_object* v_fvarId_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId(lean_object* v_fvarId_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_1082_, v_a_1084_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_addFVarId___boxed(lean_object* v_fvarId_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId(v_fvarId_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0(lean_object* v_00_u03b2_1102_, lean_object* v_m_1103_, lean_object* v_a_1104_, lean_object* v_b_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(v_m_1103_, v_a_1104_, v_b_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(lean_object* v_00_u03b2_1107_, lean_object* v_m_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v_m_1108_, v_a_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___boxed(lean_object* v_00_u03b2_1111_, lean_object* v_m_1112_, lean_object* v_a_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(v_00_u03b2_1111_, v_m_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_m_1112_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(lean_object* v_00_u03b2_1116_, lean_object* v_a_1117_, lean_object* v_x_1118_){
_start:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_1117_, v_x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1120_, lean_object* v_a_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(v_00_u03b2_1120_, v_a_1121_, v_x_1122_);
lean_dec(v_x_1122_);
lean_dec(v_a_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1(lean_object* v_00_u03b2_1125_, lean_object* v_data_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(v_data_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1128_, lean_object* v_i_1129_, lean_object* v_source_1130_, lean_object* v_target_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(v_i_1129_, v_source_1130_, v_target_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1134_, v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg(lean_object* v_fvarId_1137_, lean_object* v_x_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1147_; 
lean_inc(v_fvarId_1137_);
v___x_1147_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_1137_, v_a_1140_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_jps_1148_; lean_object* v_vars_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref_known(v___x_1147_, 1);
v_jps_1148_ = lean_ctor_get(v_a_1139_, 0);
v_vars_1149_ = lean_ctor_get(v_a_1139_, 1);
lean_inc(v_vars_1149_);
v___x_1150_ = l_Lean_FVarIdSet_insert(v_vars_1149_, v_fvarId_1137_);
lean_inc(v_jps_1148_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_jps_1148_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
lean_inc(v_a_1145_);
lean_inc_ref(v_a_1144_);
lean_inc(v_a_1143_);
lean_inc_ref(v_a_1142_);
lean_inc_ref(v_a_1141_);
lean_inc(v_a_1140_);
v___x_1152_ = lean_apply_8(v_x_1138_, v___x_1151_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, lean_box(0));
return v___x_1152_;
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_x_1138_);
lean_dec(v_fvarId_1137_);
v_a_1153_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1147_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1147_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg___boxed(lean_object* v_fvarId_1161_, lean_object* v_x_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg(v_fvarId_1161_, v_x_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withFVarId(lean_object* v_00_u03b1_1172_, lean_object* v_fvarId_1173_, lean_object* v_x_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
lean_inc(v_fvarId_1173_);
v___x_1183_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_1173_, v_a_1176_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_jps_1184_; lean_object* v_vars_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref_known(v___x_1183_, 1);
v_jps_1184_ = lean_ctor_get(v_a_1175_, 0);
v_vars_1185_ = lean_ctor_get(v_a_1175_, 1);
lean_inc(v_vars_1185_);
v___x_1186_ = l_Lean_FVarIdSet_insert(v_vars_1185_, v_fvarId_1173_);
lean_inc(v_jps_1184_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_jps_1184_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
lean_inc(v_a_1181_);
lean_inc_ref(v_a_1180_);
lean_inc(v_a_1179_);
lean_inc_ref(v_a_1178_);
lean_inc_ref(v_a_1177_);
lean_inc(v_a_1176_);
v___x_1188_ = lean_apply_8(v_x_1174_, v___x_1187_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, lean_box(0));
return v___x_1188_;
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_x_1174_);
lean_dec(v_fvarId_1173_);
v_a_1189_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1183_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1183_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withFVarId___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_fvarId_1198_, lean_object* v_x_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Compiler_LCNF_Check_Pure_withFVarId(v_00_u03b1_1197_, v_fvarId_1198_, v_x_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg(lean_object* v_fvarId_1209_, lean_object* v_x_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; 
lean_inc(v_fvarId_1209_);
v___x_1219_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_1209_, v_a_1212_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_jps_1220_; lean_object* v_vars_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref_known(v___x_1219_, 1);
v_jps_1220_ = lean_ctor_get(v_a_1211_, 0);
v_vars_1221_ = lean_ctor_get(v_a_1211_, 1);
lean_inc(v_jps_1220_);
v___x_1222_ = l_Lean_FVarIdSet_insert(v_jps_1220_, v_fvarId_1209_);
lean_inc(v_vars_1221_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v_vars_1221_);
lean_inc(v_a_1217_);
lean_inc_ref(v_a_1216_);
lean_inc(v_a_1215_);
lean_inc_ref(v_a_1214_);
lean_inc_ref(v_a_1213_);
lean_inc(v_a_1212_);
v___x_1224_ = lean_apply_8(v_x_1210_, v___x_1223_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, lean_box(0));
return v___x_1224_;
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v_x_1210_);
lean_dec(v_fvarId_1209_);
v_a_1225_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1219_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1219_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg___boxed(lean_object* v_fvarId_1233_, lean_object* v_x_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg(v_fvarId_1233_, v_x_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withJp(lean_object* v_00_u03b1_1244_, lean_object* v_fvarId_1245_, lean_object* v_x_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; 
lean_inc(v_fvarId_1245_);
v___x_1255_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_1245_, v_a_1248_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_jps_1256_; lean_object* v_vars_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1255_, 1);
v_jps_1256_ = lean_ctor_get(v_a_1247_, 0);
v_vars_1257_ = lean_ctor_get(v_a_1247_, 1);
lean_inc(v_jps_1256_);
v___x_1258_ = l_Lean_FVarIdSet_insert(v_jps_1256_, v_fvarId_1245_);
lean_inc(v_vars_1257_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v_vars_1257_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
lean_inc(v_a_1251_);
lean_inc_ref(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
v___x_1260_ = lean_apply_8(v_x_1246_, v___x_1259_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, lean_box(0));
return v___x_1260_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec_ref(v_x_1246_);
lean_dec(v_fvarId_1245_);
v_a_1261_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1255_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1255_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withJp___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_fvarId_1270_, lean_object* v_x_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Compiler_LCNF_Check_Pure_withJp(v_00_u03b1_1269_, v_fvarId_1270_, v_x_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0(lean_object* v_x1_1281_, lean_object* v_x2_1282_){
_start:
{
lean_object* v_fvarId_1283_; lean_object* v___x_1284_; 
v_fvarId_1283_ = lean_ctor_get(v_x2_1282_, 0);
lean_inc(v_fvarId_1283_);
lean_dec_ref(v_x2_1282_);
v___x_1284_ = l_Lean_FVarIdSet_insert(v_x1_1281_, v_fvarId_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1(lean_object* v_x_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_fvarId_1295_; lean_object* v___x_1296_; 
v_fvarId_1295_ = lean_ctor_get(v___y_1286_, 0);
lean_inc(v_fvarId_1295_);
lean_dec_ref(v___y_1286_);
v___x_1296_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_1295_, v___y_1288_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1___boxed(lean_object* v_x_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1(v_x_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1307_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0(void){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_instMonadEIO(lean_box(0));
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0, &l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0);
v___x_1310_ = l_StateRefT_x27_instMonad___redArg(v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg(lean_object* v_params_1336_, lean_object* v_x_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v_toApplicative_1347_; lean_object* v_toFunctor_1348_; lean_object* v_toSeq_1349_; lean_object* v_toSeqLeft_1350_; lean_object* v_toSeqRight_1351_; lean_object* v___f_1352_; lean_object* v___f_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_toApplicative_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1436_; 
v___x_1346_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1);
v_toApplicative_1347_ = lean_ctor_get(v___x_1346_, 0);
v_toFunctor_1348_ = lean_ctor_get(v_toApplicative_1347_, 0);
v_toSeq_1349_ = lean_ctor_get(v_toApplicative_1347_, 2);
v_toSeqLeft_1350_ = lean_ctor_get(v_toApplicative_1347_, 3);
v_toSeqRight_1351_ = lean_ctor_get(v_toApplicative_1347_, 4);
v___f_1352_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2));
v___f_1353_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1348_, 2);
v___f_1354_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1354_, 0, v_toFunctor_1348_);
v___f_1355_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1355_, 0, v_toFunctor_1348_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___f_1354_);
lean_ctor_set(v___x_1356_, 1, v___f_1355_);
lean_inc(v_toSeqRight_1351_);
v___f_1357_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1357_, 0, v_toSeqRight_1351_);
lean_inc(v_toSeqLeft_1350_);
v___f_1358_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1358_, 0, v_toSeqLeft_1350_);
lean_inc(v_toSeq_1349_);
v___f_1359_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1359_, 0, v_toSeq_1349_);
v___x_1360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1356_);
lean_ctor_set(v___x_1360_, 1, v___f_1352_);
lean_ctor_set(v___x_1360_, 2, v___f_1359_);
lean_ctor_set(v___x_1360_, 3, v___f_1358_);
lean_ctor_set(v___x_1360_, 4, v___f_1357_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___f_1353_);
v___x_1362_ = l_StateRefT_x27_instMonad___redArg(v___x_1361_);
v_toApplicative_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v___x_1362_, 1);
lean_dec(v_unused_1437_);
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1436_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_toApplicative_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1436_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_toFunctor_1367_; lean_object* v_toSeq_1368_; lean_object* v_toSeqLeft_1369_; lean_object* v_toSeqRight_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1434_; 
v_toFunctor_1367_ = lean_ctor_get(v_toApplicative_1363_, 0);
v_toSeq_1368_ = lean_ctor_get(v_toApplicative_1363_, 2);
v_toSeqLeft_1369_ = lean_ctor_get(v_toApplicative_1363_, 3);
v_toSeqRight_1370_ = lean_ctor_get(v_toApplicative_1363_, 4);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_toApplicative_1363_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v_toApplicative_1363_, 1);
lean_dec(v_unused_1435_);
v___x_1372_ = v_toApplicative_1363_;
v_isShared_1373_ = v_isSharedCheck_1434_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_toSeqRight_1370_);
lean_inc(v_toSeqLeft_1369_);
lean_inc(v_toSeq_1368_);
lean_inc(v_toFunctor_1367_);
lean_dec(v_toApplicative_1363_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1434_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___f_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___f_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___f_1382_; lean_object* v___x_1384_; 
v___f_1374_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4));
v___f_1375_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5));
v___f_1376_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6));
lean_inc_ref(v_toFunctor_1367_);
v___f_1377_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1377_, 0, v_toFunctor_1367_);
v___f_1378_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1378_, 0, v_toFunctor_1367_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___f_1377_);
lean_ctor_set(v___x_1379_, 1, v___f_1378_);
v___f_1380_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1380_, 0, v_toSeqRight_1370_);
v___f_1381_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1381_, 0, v_toSeqLeft_1369_);
v___f_1382_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1382_, 0, v_toSeq_1368_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___f_1380_);
lean_ctor_set(v___x_1372_, 3, v___f_1381_);
lean_ctor_set(v___x_1372_, 2, v___f_1382_);
lean_ctor_set(v___x_1372_, 1, v___f_1375_);
lean_ctor_set(v___x_1372_, 0, v___x_1379_);
v___x_1384_ = v___x_1372_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___f_1375_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v___f_1382_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v___f_1381_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v___f_1380_);
v___x_1384_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___f_1376_);
lean_ctor_set(v___x_1365_, 0, v___x_1384_);
v___x_1386_ = v___x_1365_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___f_1376_);
v___x_1386_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___y_1411_; uint8_t v___x_1420_; 
v___x_1387_ = l_ReaderT_instMonad___redArg(v___x_1386_);
v___x_1388_ = l_StateRefT_x27_instMonad___redArg(v___x_1387_);
v___x_1389_ = l_ReaderT_instMonad___redArg(v___x_1388_);
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_array_get_size(v_params_1336_);
v___x_1420_ = lean_nat_dec_lt(v___x_1390_, v___x_1391_);
if (v___x_1420_ == 0)
{
lean_dec_ref(v___x_1389_);
goto v___jp_1392_;
}
else
{
lean_object* v___f_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___f_1421_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17));
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_nat_dec_le(v___x_1391_, v___x_1391_);
if (v___x_1423_ == 0)
{
if (v___x_1420_ == 0)
{
lean_dec_ref(v___x_1389_);
goto v___jp_1392_;
}
else
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1277__overap_1426_; lean_object* v___x_1427_; 
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = lean_usize_of_nat(v___x_1391_);
lean_inc_ref(v_params_1336_);
v___x_1277__overap_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1389_, v___f_1421_, v_params_1336_, v___x_1424_, v___x_1425_, v___x_1422_);
lean_inc(v_a_1344_);
lean_inc_ref(v_a_1343_);
lean_inc(v_a_1342_);
lean_inc_ref(v_a_1341_);
lean_inc_ref(v_a_1340_);
lean_inc(v_a_1339_);
lean_inc_ref(v_a_1338_);
v___x_1427_ = lean_apply_8(v___x_1277__overap_1426_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, lean_box(0));
v___y_1411_ = v___x_1427_;
goto v___jp_1410_;
}
}
else
{
size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1281__overap_1430_; lean_object* v___x_1431_; 
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = lean_usize_of_nat(v___x_1391_);
lean_inc_ref(v_params_1336_);
v___x_1281__overap_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1389_, v___f_1421_, v_params_1336_, v___x_1428_, v___x_1429_, v___x_1422_);
lean_inc(v_a_1344_);
lean_inc_ref(v_a_1343_);
lean_inc(v_a_1342_);
lean_inc_ref(v_a_1341_);
lean_inc_ref(v_a_1340_);
lean_inc(v_a_1339_);
lean_inc_ref(v_a_1338_);
v___x_1431_ = lean_apply_8(v___x_1281__overap_1430_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, lean_box(0));
v___y_1411_ = v___x_1431_;
goto v___jp_1410_;
}
}
v___jp_1392_:
{
lean_object* v_jps_1393_; lean_object* v_vars_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_jps_1393_ = lean_ctor_get(v_a_1338_, 0);
v_vars_1394_ = lean_ctor_get(v_a_1338_, 1);
v___x_1395_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16));
v___x_1396_ = lean_nat_dec_lt(v___x_1390_, v___x_1391_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref(v_params_1336_);
lean_inc(v_a_1344_);
lean_inc_ref(v_a_1343_);
lean_inc(v_a_1342_);
lean_inc_ref(v_a_1341_);
lean_inc_ref(v_a_1340_);
lean_inc(v_a_1339_);
lean_inc_ref(v_a_1338_);
v___x_1397_ = lean_apply_8(v_x_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, lean_box(0));
return v___x_1397_;
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_nat_dec_le(v___x_1391_, v___x_1391_);
if (v___x_1398_ == 0)
{
if (v___x_1396_ == 0)
{
lean_object* v___x_1399_; 
lean_dec_ref(v_params_1336_);
lean_inc(v_a_1344_);
lean_inc_ref(v_a_1343_);
lean_inc(v_a_1342_);
lean_inc_ref(v_a_1341_);
lean_inc_ref(v_a_1340_);
lean_inc(v_a_1339_);
lean_inc_ref(v_a_1338_);
v___x_1399_ = lean_apply_8(v_x_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, lean_box(0));
return v___x_1399_;
}
else
{
size_t v___x_1400_; size_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = lean_usize_of_nat(v___x_1391_);
lean_inc(v_vars_1394_);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1395_, v___f_1374_, v_params_1336_, v___x_1400_, v___x_1401_, v_vars_1394_);
lean_inc(v_jps_1393_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_jps_1393_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
lean_inc(v_a_1344_);
lean_inc_ref(v_a_1343_);
lean_inc(v_a_1342_);
lean_inc_ref(v_a_1341_);
lean_inc_ref(v_a_1340_);
lean_inc(v_a_1339_);
v___x_1404_ = lean_apply_8(v_x_1337_, v___x_1403_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, lean_box(0));
return v___x_1404_;
}
}
else
{
size_t v___x_1405_; size_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1405_ = ((size_t)0ULL);
v___x_1406_ = lean_usize_of_nat(v___x_1391_);
lean_inc(v_vars_1394_);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1395_, v___f_1374_, v_params_1336_, v___x_1405_, v___x_1406_, v_vars_1394_);
lean_inc(v_jps_1393_);
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_jps_1393_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
lean_inc(v_a_1344_);
lean_inc_ref(v_a_1343_);
lean_inc(v_a_1342_);
lean_inc_ref(v_a_1341_);
lean_inc_ref(v_a_1340_);
lean_inc(v_a_1339_);
v___x_1409_ = lean_apply_8(v_x_1337_, v___x_1408_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, lean_box(0));
return v___x_1409_;
}
}
}
v___jp_1410_:
{
if (lean_obj_tag(v___y_1411_) == 0)
{
lean_dec_ref_known(v___y_1411_, 1);
goto v___jp_1392_;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v_x_1337_);
lean_dec_ref(v_params_1336_);
v_a_1412_ = lean_ctor_get(v___y_1411_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___y_1411_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___y_1411_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___y_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___boxed(lean_object* v_params_1438_, lean_object* v_x_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg(v_params_1438_, v_x_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams(lean_object* v_00_u03b1_1449_, lean_object* v_params_1450_, lean_object* v_x_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1460_; lean_object* v_toApplicative_1461_; lean_object* v_toFunctor_1462_; lean_object* v_toSeq_1463_; lean_object* v_toSeqLeft_1464_; lean_object* v_toSeqRight_1465_; lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___f_1471_; lean_object* v___f_1472_; lean_object* v___f_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_toApplicative_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1550_; 
v___x_1460_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1);
v_toApplicative_1461_ = lean_ctor_get(v___x_1460_, 0);
v_toFunctor_1462_ = lean_ctor_get(v_toApplicative_1461_, 0);
v_toSeq_1463_ = lean_ctor_get(v_toApplicative_1461_, 2);
v_toSeqLeft_1464_ = lean_ctor_get(v_toApplicative_1461_, 3);
v_toSeqRight_1465_ = lean_ctor_get(v_toApplicative_1461_, 4);
v___f_1466_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2));
v___f_1467_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1462_, 2);
v___f_1468_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1468_, 0, v_toFunctor_1462_);
v___f_1469_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1469_, 0, v_toFunctor_1462_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___f_1468_);
lean_ctor_set(v___x_1470_, 1, v___f_1469_);
lean_inc(v_toSeqRight_1465_);
v___f_1471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1471_, 0, v_toSeqRight_1465_);
lean_inc(v_toSeqLeft_1464_);
v___f_1472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1472_, 0, v_toSeqLeft_1464_);
lean_inc(v_toSeq_1463_);
v___f_1473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1473_, 0, v_toSeq_1463_);
v___x_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1470_);
lean_ctor_set(v___x_1474_, 1, v___f_1466_);
lean_ctor_set(v___x_1474_, 2, v___f_1473_);
lean_ctor_set(v___x_1474_, 3, v___f_1472_);
lean_ctor_set(v___x_1474_, 4, v___f_1471_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
lean_ctor_set(v___x_1475_, 1, v___f_1467_);
v___x_1476_ = l_StateRefT_x27_instMonad___redArg(v___x_1475_);
v_toApplicative_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v___x_1476_, 1);
lean_dec(v_unused_1551_);
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1550_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_toApplicative_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1550_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v_toFunctor_1481_; lean_object* v_toSeq_1482_; lean_object* v_toSeqLeft_1483_; lean_object* v_toSeqRight_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1548_; 
v_toFunctor_1481_ = lean_ctor_get(v_toApplicative_1477_, 0);
v_toSeq_1482_ = lean_ctor_get(v_toApplicative_1477_, 2);
v_toSeqLeft_1483_ = lean_ctor_get(v_toApplicative_1477_, 3);
v_toSeqRight_1484_ = lean_ctor_get(v_toApplicative_1477_, 4);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_toApplicative_1477_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_toApplicative_1477_, 1);
lean_dec(v_unused_1549_);
v___x_1486_ = v_toApplicative_1477_;
v_isShared_1487_ = v_isSharedCheck_1548_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_toSeqRight_1484_);
lean_inc(v_toSeqLeft_1483_);
lean_inc(v_toSeq_1482_);
lean_inc(v_toFunctor_1481_);
lean_dec(v_toApplicative_1477_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1548_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___f_1488_; lean_object* v___f_1489_; lean_object* v___f_1490_; lean_object* v___f_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___f_1495_; lean_object* v___f_1496_; lean_object* v___x_1498_; 
v___f_1488_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4));
v___f_1489_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5));
v___f_1490_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6));
lean_inc_ref(v_toFunctor_1481_);
v___f_1491_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1491_, 0, v_toFunctor_1481_);
v___f_1492_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1492_, 0, v_toFunctor_1481_);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___f_1491_);
lean_ctor_set(v___x_1493_, 1, v___f_1492_);
v___f_1494_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1494_, 0, v_toSeqRight_1484_);
v___f_1495_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1495_, 0, v_toSeqLeft_1483_);
v___f_1496_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1496_, 0, v_toSeq_1482_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___f_1494_);
lean_ctor_set(v___x_1486_, 3, v___f_1495_);
lean_ctor_set(v___x_1486_, 2, v___f_1496_);
lean_ctor_set(v___x_1486_, 1, v___f_1489_);
lean_ctor_set(v___x_1486_, 0, v___x_1493_);
v___x_1498_ = v___x_1486_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___f_1489_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v___f_1496_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v___f_1495_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v___f_1494_);
v___x_1498_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v___f_1490_);
lean_ctor_set(v___x_1479_, 0, v___x_1498_);
v___x_1500_ = v___x_1479_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___f_1490_);
v___x_1500_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___y_1525_; uint8_t v___x_1534_; 
v___x_1501_ = l_ReaderT_instMonad___redArg(v___x_1500_);
v___x_1502_ = l_StateRefT_x27_instMonad___redArg(v___x_1501_);
v___x_1503_ = l_ReaderT_instMonad___redArg(v___x_1502_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_array_get_size(v_params_1450_);
v___x_1534_ = lean_nat_dec_lt(v___x_1504_, v___x_1505_);
if (v___x_1534_ == 0)
{
lean_dec_ref(v___x_1503_);
goto v___jp_1506_;
}
else
{
lean_object* v___f_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___f_1535_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17));
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_nat_dec_le(v___x_1505_, v___x_1505_);
if (v___x_1537_ == 0)
{
if (v___x_1534_ == 0)
{
lean_dec_ref(v___x_1503_);
goto v___jp_1506_;
}
else
{
size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1403__overap_1540_; lean_object* v___x_1541_; 
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = lean_usize_of_nat(v___x_1505_);
lean_inc_ref(v_params_1450_);
v___x_1403__overap_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1503_, v___f_1535_, v_params_1450_, v___x_1538_, v___x_1539_, v___x_1536_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
lean_inc(v_a_1456_);
lean_inc_ref(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
v___x_1541_ = lean_apply_8(v___x_1403__overap_1540_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, lean_box(0));
v___y_1525_ = v___x_1541_;
goto v___jp_1524_;
}
}
else
{
size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1406__overap_1544_; lean_object* v___x_1545_; 
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = lean_usize_of_nat(v___x_1505_);
lean_inc_ref(v_params_1450_);
v___x_1406__overap_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1503_, v___f_1535_, v_params_1450_, v___x_1542_, v___x_1543_, v___x_1536_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
lean_inc(v_a_1456_);
lean_inc_ref(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
v___x_1545_ = lean_apply_8(v___x_1406__overap_1544_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, lean_box(0));
v___y_1525_ = v___x_1545_;
goto v___jp_1524_;
}
}
v___jp_1506_:
{
lean_object* v_jps_1507_; lean_object* v_vars_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_jps_1507_ = lean_ctor_get(v_a_1452_, 0);
v_vars_1508_ = lean_ctor_get(v_a_1452_, 1);
v___x_1509_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16));
v___x_1510_ = lean_nat_dec_lt(v___x_1504_, v___x_1505_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_dec_ref(v_params_1450_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
lean_inc(v_a_1456_);
lean_inc_ref(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
v___x_1511_ = lean_apply_8(v_x_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, lean_box(0));
return v___x_1511_;
}
else
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_nat_dec_le(v___x_1505_, v___x_1505_);
if (v___x_1512_ == 0)
{
if (v___x_1510_ == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref(v_params_1450_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
lean_inc(v_a_1456_);
lean_inc_ref(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
v___x_1513_ = lean_apply_8(v_x_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, lean_box(0));
return v___x_1513_;
}
else
{
size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1514_ = ((size_t)0ULL);
v___x_1515_ = lean_usize_of_nat(v___x_1505_);
lean_inc(v_vars_1508_);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1509_, v___f_1488_, v_params_1450_, v___x_1514_, v___x_1515_, v_vars_1508_);
lean_inc(v_jps_1507_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_jps_1507_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
lean_inc(v_a_1456_);
lean_inc_ref(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
v___x_1518_ = lean_apply_8(v_x_1451_, v___x_1517_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, lean_box(0));
return v___x_1518_;
}
}
else
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = lean_usize_of_nat(v___x_1505_);
lean_inc(v_vars_1508_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1509_, v___f_1488_, v_params_1450_, v___x_1519_, v___x_1520_, v_vars_1508_);
lean_inc(v_jps_1507_);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_jps_1507_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
lean_inc(v_a_1456_);
lean_inc_ref(v_a_1455_);
lean_inc_ref(v_a_1454_);
lean_inc(v_a_1453_);
v___x_1523_ = lean_apply_8(v_x_1451_, v___x_1522_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, lean_box(0));
return v___x_1523_;
}
}
}
v___jp_1524_:
{
if (lean_obj_tag(v___y_1525_) == 0)
{
lean_dec_ref_known(v___y_1525_, 1);
goto v___jp_1506_;
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref(v_x_1451_);
lean_dec_ref(v_params_1450_);
v_a_1526_ = lean_ctor_get(v___y_1525_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___y_1525_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___y_1525_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___y_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_withParams___boxed(lean_object* v_00_u03b1_1552_, lean_object* v_params_1553_, lean_object* v_x_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Compiler_LCNF_Check_Pure_withParams(v_00_u03b1_1552_, v_params_1553_, v_x_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(lean_object* v_as_1564_, size_t v_i_1565_, size_t v_stop_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v___x_1574_; 
v___x_1574_ = lean_usize_dec_eq(v_i_1565_, v_stop_1566_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v_fvarId_1576_; lean_object* v___x_1577_; 
v___x_1575_ = lean_array_uget_borrowed(v_as_1564_, v_i_1565_);
v_fvarId_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_fvarId_1576_);
v___x_1577_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_1576_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; size_t v___x_1579_; size_t v___x_1580_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = ((size_t)1ULL);
v___x_1580_ = lean_usize_add(v_i_1565_, v___x_1579_);
v_i_1565_ = v___x_1580_;
v_b_1567_ = v_a_1578_;
goto _start;
}
else
{
return v___x_1577_;
}
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_b_1567_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg___boxed(lean_object* v_as_1583_, lean_object* v_i_1584_, lean_object* v_stop_1585_, lean_object* v_b_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
size_t v_i_boxed_1593_; size_t v_stop_boxed_1594_; lean_object* v_res_1595_; 
v_i_boxed_1593_ = lean_unbox_usize(v_i_1584_);
lean_dec(v_i_1584_);
v_stop_boxed_1594_ = lean_unbox_usize(v_stop_1585_);
lean_dec(v_stop_1585_);
v_res_1595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_as_1583_, v_i_boxed_1593_, v_stop_boxed_1594_, v_b_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v_as_1583_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(lean_object* v_as_1596_, size_t v_i_1597_, size_t v_stop_1598_, lean_object* v_b_1599_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_usize_dec_eq(v_i_1597_, v_stop_1598_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v_fvarId_1602_; lean_object* v___x_1603_; size_t v___x_1604_; size_t v___x_1605_; 
v___x_1601_ = lean_array_uget_borrowed(v_as_1596_, v_i_1597_);
v_fvarId_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_fvarId_1602_);
v___x_1603_ = l_Lean_FVarIdSet_insert(v_b_1599_, v_fvarId_1602_);
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_add(v_i_1597_, v___x_1604_);
v_i_1597_ = v___x_1605_;
v_b_1599_ = v___x_1603_;
goto _start;
}
else
{
return v_b_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0___boxed(lean_object* v_as_1607_, lean_object* v_i_1608_, lean_object* v_stop_1609_, lean_object* v_b_1610_){
_start:
{
size_t v_i_boxed_1611_; size_t v_stop_boxed_1612_; lean_object* v_res_1613_; 
v_i_boxed_1611_ = lean_unbox_usize(v_i_1608_);
lean_dec(v_i_1608_);
v_stop_boxed_1612_ = lean_unbox_usize(v_stop_1609_);
lean_dec(v_stop_1609_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_as_1607_, v_i_boxed_1611_, v_stop_boxed_1612_, v_b_1610_);
lean_dec_ref(v_as_1607_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(lean_object* v_declName_1615_, lean_object* v_params_1616_, lean_object* v_type_1617_, lean_object* v_value_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Compiler_LCNF_Check_Pure_checkParams(v_params_1616_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___y_1798_; uint8_t v___x_1799_; 
lean_dec_ref_known(v___x_1705_, 1);
v___x_1706_ = lean_box(0);
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_array_get_size(v_params_1616_);
v___x_1799_ = lean_nat_dec_lt(v___x_1778_, v___x_1779_);
if (v___x_1799_ == 0)
{
goto v___jp_1780_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_le(v___x_1779_, v___x_1779_);
if (v___x_1800_ == 0)
{
if (v___x_1799_ == 0)
{
goto v___jp_1780_;
}
else
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = lean_usize_of_nat(v___x_1779_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_params_1616_, v___x_1801_, v___x_1802_, v___x_1706_, v_a_1620_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
v___y_1798_ = v___x_1803_;
goto v___jp_1797_;
}
}
else
{
size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = lean_usize_of_nat(v___x_1779_);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_params_1616_, v___x_1804_, v___x_1805_, v___x_1706_, v_a_1620_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
v___y_1798_ = v___x_1806_;
goto v___jp_1797_;
}
}
v___jp_1707_:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_1622_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1769_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1769_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1769_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1715_; 
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1706_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1706_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
else
{
uint8_t v___x_1717_; lean_object* v___x_1718_; 
lean_del_object(v___x_1711_);
v___x_1717_ = 0;
v___x_1718_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_1717_, v_value_1618_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_1717_, v_params_1616_, v_a_1719_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
lean_dec(v_a_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc_n(v_a_1721_, 2);
lean_dec_ref_known(v___x_1720_, 1);
lean_inc_ref(v_type_1617_);
v___x_1722_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_type_1617_, v_a_1721_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1744_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1744_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1744_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_unbox(v_a_1723_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_del_object(v___x_1725_);
v___x_1728_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5, &l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5);
v___x_1729_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
v___x_1730_ = l_Lean_MessageData_ofConstName(v_declName_1615_, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1728_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7, &l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_indentExpr(v_a_1721_);
v___x_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1735_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = l_Lean_indentExpr(v_type_1617_);
v___x_1739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_1739_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
return v___x_1740_;
}
else
{
lean_object* v___x_1742_; 
lean_dec(v_a_1723_);
lean_dec(v_a_1721_);
lean_dec_ref(v_type_1617_);
lean_dec(v_declName_1615_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1706_);
v___x_1742_ = v___x_1725_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1706_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_a_1721_);
lean_dec_ref(v_type_1617_);
lean_dec(v_declName_1615_);
v_a_1745_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1722_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1722_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_type_1617_);
lean_dec(v_declName_1615_);
v_a_1753_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1720_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1720_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
v_a_1761_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1718_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1718_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
v_a_1770_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1708_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1708_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
v___jp_1780_:
{
lean_object* v_jps_1781_; lean_object* v_vars_1782_; uint8_t v___x_1783_; 
v_jps_1781_ = lean_ctor_get(v_a_1619_, 0);
v_vars_1782_ = lean_ctor_get(v_a_1619_, 1);
v___x_1783_ = lean_nat_dec_lt(v___x_1778_, v___x_1779_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; 
lean_inc_ref(v_a_1619_);
lean_inc_ref(v_value_1618_);
v___x_1784_ = l_Lean_Compiler_LCNF_Check_Pure_check(v_value_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_dec_ref_known(v___x_1784_, 1);
goto v___jp_1707_;
}
else
{
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_dec_ref_known(v___x_1784_, 1);
goto v___jp_1707_;
}
else
{
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
return v___x_1784_;
}
}
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_nat_dec_le(v___x_1779_, v___x_1779_);
if (v___x_1785_ == 0)
{
if (v___x_1783_ == 0)
{
lean_object* v___x_1786_; 
lean_inc_ref(v_a_1619_);
lean_inc_ref(v_value_1618_);
v___x_1786_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(v_value_1618_, v___x_1706_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_dec_ref_known(v___x_1786_, 1);
v___y_1628_ = v_a_1621_;
v___y_1629_ = v_a_1622_;
v___y_1630_ = v_a_1623_;
v___y_1631_ = v_a_1624_;
v___y_1632_ = v_a_1625_;
goto v___jp_1627_;
}
else
{
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
return v___x_1786_;
}
}
else
{
size_t v___x_1787_; size_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1787_ = ((size_t)0ULL);
v___x_1788_ = lean_usize_of_nat(v___x_1779_);
lean_inc(v_vars_1782_);
v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_1616_, v___x_1787_, v___x_1788_, v_vars_1782_);
lean_inc(v_jps_1781_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_jps_1781_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
lean_inc_ref(v_value_1618_);
v___x_1791_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(v_value_1618_, v___x_1706_, v___x_1790_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_dec_ref_known(v___x_1791_, 1);
v___y_1628_ = v_a_1621_;
v___y_1629_ = v_a_1622_;
v___y_1630_ = v_a_1623_;
v___y_1631_ = v_a_1624_;
v___y_1632_ = v_a_1625_;
goto v___jp_1627_;
}
else
{
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
return v___x_1791_;
}
}
}
else
{
size_t v___x_1792_; size_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1792_ = ((size_t)0ULL);
v___x_1793_ = lean_usize_of_nat(v___x_1779_);
lean_inc(v_vars_1782_);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_1616_, v___x_1792_, v___x_1793_, v_vars_1782_);
lean_inc(v_jps_1781_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_jps_1781_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
lean_inc_ref(v_value_1618_);
v___x_1796_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(v_value_1618_, v___x_1706_, v___x_1795_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_dec_ref_known(v___x_1796_, 1);
v___y_1628_ = v_a_1621_;
v___y_1629_ = v_a_1622_;
v___y_1630_ = v_a_1623_;
v___y_1631_ = v_a_1624_;
v___y_1632_ = v_a_1625_;
goto v___jp_1627_;
}
else
{
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
return v___x_1796_;
}
}
}
}
v___jp_1797_:
{
if (lean_obj_tag(v___y_1798_) == 0)
{
lean_dec_ref_known(v___y_1798_, 1);
goto v___jp_1780_;
}
else
{
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
return v___y_1798_;
}
}
}
else
{
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
return v___x_1705_;
}
v___jp_1627_:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v___y_1629_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1696_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1696_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1696_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
uint8_t v___x_1638_; 
v___x_1638_ = lean_unbox(v_a_1634_);
lean_dec(v_a_1634_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
v___x_1639_ = lean_box(0);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
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
uint8_t v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1636_);
v___x_1643_ = 0;
v___x_1644_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_1643_, v_value_1618_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_1643_, v_params_1616_, v_a_1645_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v_a_1645_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc_n(v_a_1647_, 2);
lean_dec_ref_known(v___x_1646_, 1);
lean_inc_ref(v_type_1617_);
v___x_1648_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_type_1617_, v_a_1647_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1671_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1671_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1671_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_unbox(v_a_1649_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_del_object(v___x_1651_);
v___x_1654_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5, &l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5);
v___x_1655_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
v___x_1656_ = l_Lean_MessageData_ofConstName(v_declName_1615_, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1654_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7, &l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7);
v___x_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Lean_indentExpr(v_a_1647_);
v___x_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_indentExpr(v_type_1617_);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_1665_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1666_;
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_dec(v_a_1649_);
lean_dec(v_a_1647_);
lean_dec_ref(v_type_1617_);
lean_dec(v_declName_1615_);
v___x_1667_ = lean_box(0);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1667_);
v___x_1669_ = v___x_1651_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_a_1647_);
lean_dec_ref(v_type_1617_);
lean_dec(v_declName_1615_);
v_a_1672_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1648_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1648_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v_type_1617_);
lean_dec(v_declName_1615_);
v_a_1680_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1646_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1646_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
v_a_1688_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1644_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1644_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_value_1618_);
lean_dec_ref(v_type_1617_);
lean_dec_ref(v_params_1616_);
lean_dec(v_declName_1615_);
v_a_1697_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1633_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1633_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0));
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2));
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4));
v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6));
v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8));
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(lean_object* v_funDecl_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_fvarId_1831_; lean_object* v_binderName_1832_; lean_object* v_params_1833_; lean_object* v_type_1834_; lean_object* v_value_1835_; lean_object* v___x_1836_; 
v_fvarId_1831_ = lean_ctor_get(v_funDecl_1822_, 0);
v_binderName_1832_ = lean_ctor_get(v_funDecl_1822_, 1);
lean_inc_n(v_binderName_1832_, 2);
v_params_1833_ = lean_ctor_get(v_funDecl_1822_, 2);
v_type_1834_ = lean_ctor_get(v_funDecl_1822_, 3);
v_value_1835_ = lean_ctor_get(v_funDecl_1822_, 4);
lean_inc_ref(v_value_1835_);
lean_inc_ref(v_type_1834_);
lean_inc_ref(v_params_1833_);
v___x_1836_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(v_binderName_1832_, v_params_1833_, v_type_1834_, v_value_1835_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
if (lean_obj_tag(v___x_1836_) == 0)
{
uint8_t v___x_1837_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___x_1868_; 
lean_dec_ref_known(v___x_1836_, 1);
v___x_1837_ = 0;
lean_inc(v_fvarId_1831_);
v___x_1868_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_1837_, v_fvarId_1831_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v_binderName_1870_; lean_object* v_type_1871_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; uint8_t v___x_1890_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v_binderName_1870_ = lean_ctor_get(v_a_1869_, 1);
lean_inc(v_binderName_1870_);
v_type_1871_ = lean_ctor_get(v_a_1869_, 3);
lean_inc_ref(v_type_1871_);
lean_dec(v_a_1869_);
v___x_1890_ = lean_name_eq(v_binderName_1870_, v_binderName_1832_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1891_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1);
lean_inc(v_binderName_1832_);
v___x_1892_ = l_Lean_MessageData_ofName(v_binderName_1832_);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9, &l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_MessageData_ofName(v_binderName_1870_);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3, &l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_1899_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_dec_ref_known(v___x_1900_, 1);
v___y_1873_ = v_a_1826_;
v___y_1874_ = v_a_1827_;
v___y_1875_ = v_a_1828_;
v___y_1876_ = v_a_1829_;
goto v___jp_1872_;
}
else
{
lean_dec_ref(v_type_1871_);
lean_dec(v_binderName_1832_);
lean_dec_ref(v_funDecl_1822_);
return v___x_1900_;
}
}
else
{
lean_dec(v_binderName_1870_);
v___y_1873_ = v_a_1826_;
v___y_1874_ = v_a_1827_;
v___y_1875_ = v_a_1828_;
v___y_1876_ = v_a_1829_;
goto v___jp_1872_;
}
v___jp_1872_:
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_expr_eqv(v_type_1871_, v_type_1834_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1878_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1);
lean_inc(v_binderName_1832_);
v___x_1879_ = l_Lean_MessageData_ofName(v_binderName_1832_);
v___x_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5, &l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lean_indentExpr(v_type_1871_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7, &l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
lean_inc_ref(v_type_1834_);
v___x_1887_ = l_Lean_indentExpr(v_type_1834_);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_1888_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_dec_ref_known(v___x_1889_, 1);
v___y_1839_ = v___y_1873_;
v___y_1840_ = v___y_1874_;
v___y_1841_ = v___y_1875_;
v___y_1842_ = v___y_1876_;
goto v___jp_1838_;
}
else
{
lean_dec(v_binderName_1832_);
lean_dec_ref(v_funDecl_1822_);
return v___x_1889_;
}
}
else
{
lean_dec_ref(v_type_1871_);
v___y_1839_ = v___y_1873_;
v___y_1840_ = v___y_1874_;
v___y_1841_ = v___y_1875_;
v___y_1842_ = v___y_1876_;
goto v___jp_1838_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_binderName_1832_);
lean_dec_ref(v_funDecl_1822_);
v_a_1901_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1868_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1868_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
v___jp_1838_:
{
lean_object* v___x_1843_; 
lean_inc(v_fvarId_1831_);
v___x_1843_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_1837_, v_fvarId_1831_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1859_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1859_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1859_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; 
v___x_1848_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(v___x_1837_, v_a_1844_, v_funDecl_1822_);
lean_dec_ref(v_funDecl_1822_);
lean_dec(v_a_1844_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_del_object(v___x_1846_);
v___x_1849_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1);
v___x_1850_ = l_Lean_MessageData_ofName(v_binderName_1832_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3, &l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_1853_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec(v_binderName_1832_);
v___x_1855_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1855_);
v___x_1857_ = v___x_1846_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_binderName_1832_);
lean_dec_ref(v_funDecl_1822_);
v_a_1860_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1843_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1843_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
lean_dec(v_binderName_1832_);
lean_dec_ref(v_funDecl_1822_);
return v___x_1836_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__2(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_check___closed__1));
v___x_1911_ = l_Lean_stringToMessageData(v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__4(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_check___closed__3));
v___x_1914_ = l_Lean_stringToMessageData(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__6(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_check___closed__5));
v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
return v___x_1917_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__8(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_check___closed__7));
v___x_1920_ = l_Lean_stringToMessageData(v___x_1919_);
return v___x_1920_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0(void){
_start:
{
uint8_t v_hasDefault_1921_; lean_object* v_ctorNames_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_hasDefault_1921_ = 0;
v_ctorNames_1922_ = l_Lean_NameSet_empty;
v___x_1923_ = lean_box(v_hasDefault_1921_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_ctorNames_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__0));
v___x_1927_ = l_Lean_stringToMessageData(v___x_1926_);
return v___x_1927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__2));
v___x_1930_ = l_Lean_stringToMessageData(v___x_1929_);
return v___x_1930_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__4));
v___x_1933_ = l_Lean_stringToMessageData(v___x_1932_);
return v___x_1933_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__6));
v___x_1936_ = l_Lean_stringToMessageData(v___x_1935_);
return v___x_1936_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__9(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__8));
v___x_1939_ = l_Lean_stringToMessageData(v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__11(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__10));
v___x_1942_ = l_Lean_stringToMessageData(v___x_1941_);
return v___x_1942_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__13(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__12));
v___x_1945_ = l_Lean_stringToMessageData(v___x_1944_);
return v___x_1945_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__15(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__14));
v___x_1948_ = l_Lean_stringToMessageData(v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(lean_object* v_typeName_1949_, lean_object* v_as_1950_, size_t v_sz_1951_, size_t v_i_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_a_1963_; uint8_t v___x_1967_; 
v___x_1967_ = lean_usize_dec_lt(v_i_1952_, v_sz_1951_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
lean_dec(v_typeName_1949_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_b_1953_);
return v___x_1968_;
}
else
{
lean_object* v_fst_1969_; lean_object* v_snd_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2219_; 
v_fst_1969_ = lean_ctor_get(v_b_1953_, 0);
v_snd_1970_ = lean_ctor_get(v_b_1953_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_b_1953_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_1972_ = v_b_1953_;
v_isShared_1973_ = v_isSharedCheck_2219_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1970_);
lean_inc(v_fst_1969_);
lean_dec(v_b_1953_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2219_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v_a_1988_; 
v_a_1988_ = lean_array_uget_borrowed(v_as_1950_, v_i_1952_);
if (lean_obj_tag(v_a_1988_) == 0)
{
lean_object* v_ctorName_1989_; lean_object* v_params_1990_; lean_object* v_code_1991_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2062_; lean_object* v_numFields_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v_induct_2108_; lean_object* v_numFields_2109_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___x_2183_; 
v_ctorName_1989_ = lean_ctor_get(v_a_1988_, 0);
v_params_1990_ = lean_ctor_get(v_a_1988_, 1);
v_code_1991_ = lean_ctor_get(v_a_1988_, 2);
v___x_2183_ = l_Lean_Compiler_LCNF_Check_Pure_checkParams(v_params_1990_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_2183_) == 0)
{
uint8_t v___x_2184_; 
lean_dec_ref_known(v___x_2183_, 1);
v___x_2184_ = l_Lean_NameSet_contains(v_fst_1969_, v_ctorName_1989_);
if (v___x_2184_ == 0)
{
v___y_2168_ = v___y_1954_;
v___y_2169_ = v___y_1955_;
v___y_2170_ = v___y_1956_;
v___y_2171_ = v___y_1957_;
v___y_2172_ = v___y_1958_;
v___y_2173_ = v___y_1959_;
v___y_2174_ = v___y_1960_;
goto v___jp_2167_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2185_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__13);
lean_inc(v_ctorName_1989_);
v___x_2186_ = l_Lean_MessageData_ofName(v_ctorName_1989_);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__15);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_2189_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_dec_ref_known(v___x_2190_, 1);
v___y_2168_ = v___y_1954_;
v___y_2169_ = v___y_1955_;
v___y_2170_ = v___y_1956_;
v___y_2171_ = v___y_1957_;
v___y_2172_ = v___y_1958_;
v___y_2173_ = v___y_1959_;
v___y_2174_ = v___y_1960_;
goto v___jp_2167_;
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_del_object(v___x_1972_);
lean_dec(v_snd_1970_);
lean_dec(v_fst_1969_);
lean_dec(v_typeName_1949_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_del_object(v___x_1972_);
lean_dec(v_snd_1970_);
lean_dec(v_fst_1969_);
lean_dec(v_typeName_1949_);
v_a_2199_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2183_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2183_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
v___jp_1992_:
{
lean_object* v_jps_2003_; lean_object* v_vars_2004_; uint8_t v___x_2005_; 
v_jps_2003_ = lean_ctor_get(v___y_1994_, 0);
v_vars_2004_ = lean_ctor_get(v___y_1994_, 1);
v___x_2005_ = lean_nat_dec_lt(v___y_1993_, v___y_1995_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec(v___y_1995_);
lean_inc(v_vars_2004_);
lean_inc(v_jps_2003_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_jps_2003_);
lean_ctor_set(v___x_2006_, 1, v_vars_2004_);
lean_inc_ref(v_code_1991_);
v___x_2007_ = l_Lean_Compiler_LCNF_Check_Pure_check(v_code_1991_, v___x_2006_, v___y_1999_, v___y_2000_, v___y_2002_, v___y_2001_, v___y_1996_, v___y_1997_);
v___y_1975_ = v___y_1998_;
v___y_1976_ = v___x_2007_;
goto v___jp_1974_;
}
else
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_nat_dec_le(v___y_1995_, v___y_1995_);
if (v___x_2008_ == 0)
{
if (v___x_2005_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v___y_1995_);
lean_inc(v_vars_2004_);
lean_inc(v_jps_2003_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_jps_2003_);
lean_ctor_set(v___x_2009_, 1, v_vars_2004_);
lean_inc_ref(v_code_1991_);
v___x_2010_ = l_Lean_Compiler_LCNF_Check_Pure_check(v_code_1991_, v___x_2009_, v___y_1999_, v___y_2000_, v___y_2002_, v___y_2001_, v___y_1996_, v___y_1997_);
v___y_1975_ = v___y_1998_;
v___y_1976_ = v___x_2010_;
goto v___jp_1974_;
}
else
{
size_t v___x_2011_; size_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = lean_usize_of_nat(v___y_1995_);
lean_dec(v___y_1995_);
lean_inc(v_vars_2004_);
v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_1990_, v___x_2011_, v___x_2012_, v_vars_2004_);
lean_inc(v_jps_2003_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_jps_2003_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
lean_inc_ref(v_code_1991_);
v___x_2015_ = l_Lean_Compiler_LCNF_Check_Pure_check(v_code_1991_, v___x_2014_, v___y_1999_, v___y_2000_, v___y_2002_, v___y_2001_, v___y_1996_, v___y_1997_);
v___y_1975_ = v___y_1998_;
v___y_1976_ = v___x_2015_;
goto v___jp_1974_;
}
}
else
{
size_t v___x_2016_; size_t v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2016_ = ((size_t)0ULL);
v___x_2017_ = lean_usize_of_nat(v___y_1995_);
lean_dec(v___y_1995_);
lean_inc(v_vars_2004_);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_1990_, v___x_2016_, v___x_2017_, v_vars_2004_);
lean_inc(v_jps_2003_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v_jps_2003_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
lean_inc_ref(v_code_1991_);
v___x_2020_ = l_Lean_Compiler_LCNF_Check_Pure_check(v_code_1991_, v___x_2019_, v___y_1999_, v___y_2000_, v___y_2002_, v___y_2001_, v___y_1996_, v___y_1997_);
v___y_1975_ = v___y_1998_;
v___y_1976_ = v___x_2020_;
goto v___jp_1974_;
}
}
}
v___jp_2021_:
{
if (lean_obj_tag(v___y_2032_) == 0)
{
lean_dec_ref_known(v___y_2032_, 1);
v___y_1993_ = v___y_2023_;
v___y_1994_ = v___y_2022_;
v___y_1995_ = v___y_2024_;
v___y_1996_ = v___y_2025_;
v___y_1997_ = v___y_2026_;
v___y_1998_ = v___y_2027_;
v___y_1999_ = v___y_2028_;
v___y_2000_ = v___y_2029_;
v___y_2001_ = v___y_2030_;
v___y_2002_ = v___y_2031_;
goto v___jp_1992_;
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v___y_2027_);
lean_dec(v___y_2024_);
lean_del_object(v___x_1972_);
lean_dec(v_snd_1970_);
lean_dec(v_typeName_1949_);
v_a_2033_ = lean_ctor_get(v___y_2032_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___y_2032_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___y_2032_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___y_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
v___jp_2041_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_array_get_size(v_params_1990_);
v___x_2052_ = lean_nat_dec_lt(v___x_2050_, v___x_2051_);
if (v___x_2052_ == 0)
{
v___y_1993_ = v___x_2050_;
v___y_1994_ = v___y_2043_;
v___y_1995_ = v___x_2051_;
v___y_1996_ = v___y_2048_;
v___y_1997_ = v___y_2049_;
v___y_1998_ = v___y_2042_;
v___y_1999_ = v___y_2044_;
v___y_2000_ = v___y_2045_;
v___y_2001_ = v___y_2047_;
v___y_2002_ = v___y_2046_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = lean_nat_dec_le(v___x_2051_, v___x_2051_);
if (v___x_2054_ == 0)
{
if (v___x_2052_ == 0)
{
v___y_1993_ = v___x_2050_;
v___y_1994_ = v___y_2043_;
v___y_1995_ = v___x_2051_;
v___y_1996_ = v___y_2048_;
v___y_1997_ = v___y_2049_;
v___y_1998_ = v___y_2042_;
v___y_1999_ = v___y_2044_;
v___y_2000_ = v___y_2045_;
v___y_2001_ = v___y_2047_;
v___y_2002_ = v___y_2046_;
goto v___jp_1992_;
}
else
{
size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = ((size_t)0ULL);
v___x_2056_ = lean_usize_of_nat(v___x_2051_);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_params_1990_, v___x_2055_, v___x_2056_, v___x_2053_, v___y_2044_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
v___y_2022_ = v___y_2043_;
v___y_2023_ = v___x_2050_;
v___y_2024_ = v___x_2051_;
v___y_2025_ = v___y_2048_;
v___y_2026_ = v___y_2049_;
v___y_2027_ = v___y_2042_;
v___y_2028_ = v___y_2044_;
v___y_2029_ = v___y_2045_;
v___y_2030_ = v___y_2047_;
v___y_2031_ = v___y_2046_;
v___y_2032_ = v___x_2057_;
goto v___jp_2021_;
}
}
else
{
size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = ((size_t)0ULL);
v___x_2059_ = lean_usize_of_nat(v___x_2051_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_params_1990_, v___x_2058_, v___x_2059_, v___x_2053_, v___y_2044_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
v___y_2022_ = v___y_2043_;
v___y_2023_ = v___x_2050_;
v___y_2024_ = v___x_2051_;
v___y_2025_ = v___y_2048_;
v___y_2026_ = v___y_2049_;
v___y_2027_ = v___y_2042_;
v___y_2028_ = v___y_2044_;
v___y_2029_ = v___y_2045_;
v___y_2030_ = v___y_2047_;
v___y_2031_ = v___y_2046_;
v___y_2032_ = v___x_2060_;
goto v___jp_2021_;
}
}
}
v___jp_2061_:
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = lean_array_get_size(v_params_1990_);
v___x_2072_ = lean_nat_dec_eq(v___x_2071_, v_numFields_2063_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1);
lean_inc(v_ctorName_1989_);
v___x_2074_ = l_Lean_MessageData_ofName(v_ctorName_1989_);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__3);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Nat_reprFast(v_numFields_2063_);
v___x_2079_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
v___x_2080_ = l_Lean_MessageData_ofFormat(v___x_2079_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2077_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__5);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = l_Nat_reprFast(v___x_2071_);
v___x_2085_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
v___x_2086_ = l_Lean_MessageData_ofFormat(v___x_2085_);
v___x_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2083_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__7);
v___x_2089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_2089_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_dec_ref_known(v___x_2090_, 1);
v___y_2042_ = v___y_2062_;
v___y_2043_ = v___y_2064_;
v___y_2044_ = v___y_2065_;
v___y_2045_ = v___y_2066_;
v___y_2046_ = v___y_2067_;
v___y_2047_ = v___y_2068_;
v___y_2048_ = v___y_2069_;
v___y_2049_ = v___y_2070_;
goto v___jp_2041_;
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v___y_2062_);
lean_del_object(v___x_1972_);
lean_dec(v_snd_1970_);
lean_dec(v_typeName_1949_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_dec(v_numFields_2063_);
v___y_2042_ = v___y_2062_;
v___y_2043_ = v___y_2064_;
v___y_2044_ = v___y_2065_;
v___y_2045_ = v___y_2066_;
v___y_2046_ = v___y_2067_;
v___y_2047_ = v___y_2068_;
v___y_2048_ = v___y_2069_;
v___y_2049_ = v___y_2070_;
goto v___jp_2041_;
}
}
v___jp_2099_:
{
uint8_t v___x_2110_; 
v___x_2110_ = lean_name_eq(v_induct_2108_, v_typeName_1949_);
lean_dec(v_induct_2108_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2111_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1);
lean_inc(v_ctorName_1989_);
v___x_2112_ = l_Lean_MessageData_ofName(v_ctorName_1989_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__9);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
lean_inc(v_typeName_1949_);
v___x_2116_ = l_Lean_MessageData_ofName(v_typeName_1949_);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3, &l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__3);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_2119_, v___y_2106_, v___y_2103_, v___y_2101_, v___y_2104_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_dec_ref_known(v___x_2120_, 1);
v___y_2062_ = v___y_2102_;
v_numFields_2063_ = v_numFields_2109_;
v___y_2064_ = v___y_2105_;
v___y_2065_ = v___y_2107_;
v___y_2066_ = v___y_2100_;
v___y_2067_ = v___y_2106_;
v___y_2068_ = v___y_2103_;
v___y_2069_ = v___y_2101_;
v___y_2070_ = v___y_2104_;
goto v___jp_2061_;
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_numFields_2109_);
lean_dec(v___y_2102_);
lean_del_object(v___x_1972_);
lean_dec(v_snd_1970_);
lean_dec(v_typeName_1949_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
v___y_2062_ = v___y_2102_;
v_numFields_2063_ = v_numFields_2109_;
v___y_2064_ = v___y_2105_;
v___y_2065_ = v___y_2107_;
v___y_2066_ = v___y_2100_;
v___y_2067_ = v___y_2106_;
v___y_2068_ = v___y_2103_;
v___y_2069_ = v___y_2101_;
v___y_2070_ = v___y_2104_;
goto v___jp_2061_;
}
}
v___jp_2129_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2135_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__1);
lean_inc(v_ctorName_1989_);
v___x_2136_ = l_Lean_MessageData_ofName(v_ctorName_1989_);
v___x_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___closed__11);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_2139_, v___y_2134_, v___y_2132_, v___y_2130_, v___y_2133_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v___x_2141_; 
lean_dec_ref_known(v___x_2140_, 1);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___y_2131_);
lean_ctor_set(v___x_2141_, 1, v_snd_1970_);
v_a_1963_ = v___x_2141_;
goto v___jp_1962_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v___y_2131_);
lean_dec(v_snd_1970_);
lean_dec(v_typeName_1949_);
v_a_2142_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2140_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2140_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
v___jp_2150_:
{
uint8_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = 0;
lean_inc(v_ctorName_1989_);
lean_inc_ref(v___y_2156_);
v___x_2161_ = l_Lean_Environment_find_x3f(v___y_2156_, v_ctorName_1989_, v___x_2160_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_dec_ref(v___y_2156_);
lean_del_object(v___x_1972_);
v___y_2130_ = v___y_2152_;
v___y_2131_ = v___y_2153_;
v___y_2132_ = v___y_2154_;
v___y_2133_ = v___y_2155_;
v___y_2134_ = v___y_2158_;
goto v___jp_2129_;
}
else
{
lean_object* v_val_2162_; 
v_val_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_val_2162_);
lean_dec_ref_known(v___x_2161_, 1);
if (lean_obj_tag(v_val_2162_) == 6)
{
lean_object* v_val_2163_; lean_object* v_induct_2164_; lean_object* v_numFields_2165_; uint8_t v___x_2166_; 
v_val_2163_ = lean_ctor_get(v_val_2162_, 0);
lean_inc_ref(v_val_2163_);
lean_dec_ref_known(v_val_2162_, 1);
v_induct_2164_ = lean_ctor_get(v_val_2163_, 1);
lean_inc_n(v_induct_2164_, 2);
v_numFields_2165_ = lean_ctor_get(v_val_2163_, 4);
lean_inc(v_numFields_2165_);
lean_dec_ref(v_val_2163_);
v___x_2166_ = l_Lean_Compiler_hasInductiveOverride(v___y_2156_, v_induct_2164_);
if (v___x_2166_ == 0)
{
v___y_2100_ = v___y_2151_;
v___y_2101_ = v___y_2152_;
v___y_2102_ = v___y_2153_;
v___y_2103_ = v___y_2154_;
v___y_2104_ = v___y_2155_;
v___y_2105_ = v___y_2157_;
v___y_2106_ = v___y_2158_;
v___y_2107_ = v___y_2159_;
v_induct_2108_ = v_induct_2164_;
v_numFields_2109_ = v_numFields_2165_;
goto v___jp_2099_;
}
else
{
lean_dec(v_numFields_2165_);
lean_dec(v_induct_2164_);
lean_del_object(v___x_1972_);
v___y_2130_ = v___y_2152_;
v___y_2131_ = v___y_2153_;
v___y_2132_ = v___y_2154_;
v___y_2133_ = v___y_2155_;
v___y_2134_ = v___y_2158_;
goto v___jp_2129_;
}
}
else
{
lean_dec(v_val_2162_);
lean_dec_ref(v___y_2156_);
lean_del_object(v___x_1972_);
v___y_2130_ = v___y_2152_;
v___y_2131_ = v___y_2153_;
v___y_2132_ = v___y_2154_;
v___y_2133_ = v___y_2155_;
v___y_2134_ = v___y_2158_;
goto v___jp_2129_;
}
}
}
v___jp_2167_:
{
lean_object* v___x_2175_; lean_object* v_env_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = lean_st_ref_get(v___y_2174_);
v_env_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc_ref_n(v_env_2176_, 2);
lean_dec(v___x_2175_);
lean_inc_n(v_ctorName_1989_, 2);
v___x_2177_ = l_Lean_NameSet_insert(v_fst_1969_, v_ctorName_1989_);
v___x_2178_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_2176_, v_ctorName_1989_);
if (lean_obj_tag(v___x_2178_) == 1)
{
lean_object* v_val_2179_; 
v_val_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v___x_2178_, 1);
if (lean_obj_tag(v_val_2179_) == 2)
{
lean_object* v_info_2180_; lean_object* v_induct_2181_; lean_object* v_numFields_2182_; 
lean_dec_ref(v_env_2176_);
v_info_2180_ = lean_ctor_get(v_val_2179_, 1);
lean_inc_ref(v_info_2180_);
lean_dec_ref_known(v_val_2179_, 2);
v_induct_2181_ = lean_ctor_get(v_info_2180_, 0);
lean_inc(v_induct_2181_);
v_numFields_2182_ = lean_ctor_get(v_info_2180_, 3);
lean_inc(v_numFields_2182_);
lean_dec_ref(v_info_2180_);
v___y_2100_ = v___y_2170_;
v___y_2101_ = v___y_2173_;
v___y_2102_ = v___x_2177_;
v___y_2103_ = v___y_2172_;
v___y_2104_ = v___y_2174_;
v___y_2105_ = v___y_2168_;
v___y_2106_ = v___y_2171_;
v___y_2107_ = v___y_2169_;
v_induct_2108_ = v_induct_2181_;
v_numFields_2109_ = v_numFields_2182_;
goto v___jp_2099_;
}
else
{
lean_dec(v_val_2179_);
v___y_2151_ = v___y_2170_;
v___y_2152_ = v___y_2173_;
v___y_2153_ = v___x_2177_;
v___y_2154_ = v___y_2172_;
v___y_2155_ = v___y_2174_;
v___y_2156_ = v_env_2176_;
v___y_2157_ = v___y_2168_;
v___y_2158_ = v___y_2171_;
v___y_2159_ = v___y_2169_;
goto v___jp_2150_;
}
}
else
{
lean_dec(v___x_2178_);
v___y_2151_ = v___y_2170_;
v___y_2152_ = v___y_2173_;
v___y_2153_ = v___x_2177_;
v___y_2154_ = v___y_2172_;
v___y_2155_ = v___y_2174_;
v___y_2156_ = v_env_2176_;
v___y_2157_ = v___y_2168_;
v___y_2158_ = v___y_2171_;
v___y_2159_ = v___y_2169_;
goto v___jp_2150_;
}
}
}
else
{
lean_object* v_code_2207_; lean_object* v___x_2208_; 
lean_del_object(v___x_1972_);
lean_dec(v_snd_1970_);
v_code_2207_ = lean_ctor_get(v_a_1988_, 0);
lean_inc_ref(v___y_1954_);
lean_inc_ref(v_code_2207_);
v___x_2208_ = l_Lean_Compiler_LCNF_Check_Pure_check(v_code_2207_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec_ref_known(v___x_2208_, 1);
v___x_2209_ = lean_box(v___x_1967_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_fst_1969_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v_a_1963_ = v___x_2210_;
goto v___jp_1962_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_fst_1969_);
lean_dec(v_typeName_1949_);
v_a_2211_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2208_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2208_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
v___jp_1974_:
{
if (lean_obj_tag(v___y_1976_) == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref_known(v___y_1976_, 1);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___y_1975_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___y_1975_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_snd_1970_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
v_a_1963_ = v___x_1978_;
goto v___jp_1962_;
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v___y_1975_);
lean_del_object(v___x_1972_);
lean_dec(v_snd_1970_);
lean_dec(v_typeName_1949_);
v_a_1980_ = lean_ctor_get(v___y_1976_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___y_1976_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___y_1976_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___y_1976_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
v___jp_1962_:
{
size_t v___x_1964_; size_t v___x_1965_; 
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_i_1952_, v___x_1964_);
v_i_1952_ = v___x_1965_;
v_b_1953_ = v_a_1963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkCases(lean_object* v_c_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_typeName_2229_; lean_object* v_discr_2230_; lean_object* v_alts_2231_; lean_object* v___x_2232_; 
v_typeName_2229_ = lean_ctor_get(v_c_2220_, 0);
lean_inc(v_typeName_2229_);
v_discr_2230_ = lean_ctor_get(v_c_2220_, 2);
lean_inc(v_discr_2230_);
v_alts_2231_ = lean_ctor_get(v_c_2220_, 3);
lean_inc_ref(v_alts_2231_);
lean_dec_ref(v_c_2220_);
v___x_2232_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(v_discr_2230_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v___x_2233_; size_t v_sz_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
lean_dec_ref_known(v___x_2232_, 1);
v___x_2233_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0, &l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0_once, _init_l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0);
v_sz_2234_ = lean_array_size(v_alts_2231_);
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(v_typeName_2229_, v_alts_2231_, v_sz_2234_, v___x_2235_, v___x_2233_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
lean_dec_ref(v_alts_2231_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2244_; 
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v___x_2236_, 0);
lean_dec(v_unused_2245_);
v___x_2238_ = v___x_2236_;
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
else
{
lean_dec(v___x_2236_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = lean_box(0);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
v_a_2246_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2236_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2236_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_dec_ref(v_alts_2231_);
lean_dec(v_typeName_2229_);
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_check(lean_object* v_code_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_check___closed__0));
v___x_2264_ = l_Lean_Core_checkSystem(v___x_2263_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2385_; 
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v___x_2264_, 0);
lean_dec(v_unused_2386_);
v___x_2266_ = v___x_2264_;
v_isShared_2267_ = v_isSharedCheck_2385_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v___x_2264_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2385_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
switch(lean_obj_tag(v_code_2254_))
{
case 0:
{
lean_object* v_decl_2268_; lean_object* v_k_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2283_; 
lean_del_object(v___x_2266_);
v_decl_2268_ = lean_ctor_get(v_code_2254_, 0);
v_k_2269_ = lean_ctor_get(v_code_2254_, 1);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_code_2254_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2271_ = v_code_2254_;
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_k_2269_);
lean_inc(v_decl_2268_);
lean_dec(v_code_2254_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; 
lean_inc_ref(v_decl_2268_);
v___x_2273_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(v_decl_2268_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_fvarId_2274_; lean_object* v___x_2275_; 
lean_dec_ref_known(v___x_2273_, 1);
v_fvarId_2274_ = lean_ctor_get(v_decl_2268_, 0);
lean_inc_n(v_fvarId_2274_, 2);
lean_dec_ref(v_decl_2268_);
v___x_2275_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_2274_, v_a_2256_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_jps_2276_; lean_object* v_vars_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
lean_dec_ref_known(v___x_2275_, 1);
v_jps_2276_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_jps_2276_);
v_vars_2277_ = lean_ctor_get(v_a_2255_, 1);
lean_inc(v_vars_2277_);
lean_dec_ref(v_a_2255_);
v___x_2278_ = l_Lean_FVarIdSet_insert(v_vars_2277_, v_fvarId_2274_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 1, v___x_2278_);
lean_ctor_set(v___x_2271_, 0, v_jps_2276_);
v___x_2280_ = v___x_2271_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_jps_2276_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
v_code_2254_ = v_k_2269_;
v_a_2255_ = v___x_2280_;
goto _start;
}
}
else
{
lean_dec(v_fvarId_2274_);
lean_del_object(v___x_2271_);
lean_dec_ref(v_k_2269_);
lean_dec_ref(v_a_2255_);
return v___x_2275_;
}
}
else
{
lean_del_object(v___x_2271_);
lean_dec_ref(v_k_2269_);
lean_dec_ref(v_decl_2268_);
lean_dec_ref(v_a_2255_);
return v___x_2273_;
}
}
}
case 1:
{
lean_object* v_decl_2284_; lean_object* v_k_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2301_; 
lean_del_object(v___x_2266_);
v_decl_2284_ = lean_ctor_get(v_code_2254_, 0);
v_k_2285_ = lean_ctor_get(v_code_2254_, 1);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_code_2254_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2287_ = v_code_2254_;
v_isShared_2288_ = v_isSharedCheck_2301_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_k_2285_);
lean_inc(v_decl_2284_);
lean_dec(v_code_2254_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2301_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v_jps_2289_; lean_object* v_vars_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v_jps_2289_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_jps_2289_);
v_vars_2290_ = lean_ctor_get(v_a_2255_, 1);
lean_inc_n(v_vars_2290_, 2);
lean_dec_ref(v_a_2255_);
v___x_2291_ = lean_box(1);
if (v_isShared_2288_ == 0)
{
lean_ctor_set_tag(v___x_2287_, 0);
lean_ctor_set(v___x_2287_, 1, v_vars_2290_);
lean_ctor_set(v___x_2287_, 0, v___x_2291_);
v___x_2293_ = v___x_2287_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_vars_2290_);
v___x_2293_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; 
lean_inc_ref(v_decl_2284_);
v___x_2294_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(v_decl_2284_, v___x_2293_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v___x_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_fvarId_2295_; lean_object* v___x_2296_; 
lean_dec_ref_known(v___x_2294_, 1);
v_fvarId_2295_ = lean_ctor_get(v_decl_2284_, 0);
lean_inc_n(v_fvarId_2295_, 2);
lean_dec_ref(v_decl_2284_);
v___x_2296_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_2295_, v_a_2256_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref_known(v___x_2296_, 1);
v___x_2297_ = l_Lean_FVarIdSet_insert(v_vars_2290_, v_fvarId_2295_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_jps_2289_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v_code_2254_ = v_k_2285_;
v_a_2255_ = v___x_2298_;
goto _start;
}
else
{
lean_dec(v_fvarId_2295_);
lean_dec(v_vars_2290_);
lean_dec(v_jps_2289_);
lean_dec_ref(v_k_2285_);
return v___x_2296_;
}
}
else
{
lean_dec(v_vars_2290_);
lean_dec(v_jps_2289_);
lean_dec_ref(v_k_2285_);
lean_dec_ref(v_decl_2284_);
return v___x_2294_;
}
}
}
}
case 2:
{
lean_object* v_decl_2302_; lean_object* v_k_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2317_; 
lean_del_object(v___x_2266_);
v_decl_2302_ = lean_ctor_get(v_code_2254_, 0);
v_k_2303_ = lean_ctor_get(v_code_2254_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_code_2254_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2305_ = v_code_2254_;
v_isShared_2306_ = v_isSharedCheck_2317_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_k_2303_);
lean_inc(v_decl_2302_);
lean_dec(v_code_2254_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2317_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; 
lean_inc_ref(v_decl_2302_);
v___x_2307_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(v_decl_2302_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_fvarId_2308_; lean_object* v___x_2309_; 
lean_dec_ref_known(v___x_2307_, 1);
v_fvarId_2308_ = lean_ctor_get(v_decl_2302_, 0);
lean_inc_n(v_fvarId_2308_, 2);
lean_dec_ref(v_decl_2302_);
v___x_2309_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(v_fvarId_2308_, v_a_2256_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_jps_2310_; lean_object* v_vars_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
lean_dec_ref_known(v___x_2309_, 1);
v_jps_2310_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_jps_2310_);
v_vars_2311_ = lean_ctor_get(v_a_2255_, 1);
lean_inc(v_vars_2311_);
lean_dec_ref(v_a_2255_);
v___x_2312_ = l_Lean_FVarIdSet_insert(v_jps_2310_, v_fvarId_2308_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set_tag(v___x_2305_, 0);
lean_ctor_set(v___x_2305_, 1, v_vars_2311_);
lean_ctor_set(v___x_2305_, 0, v___x_2312_);
v___x_2314_ = v___x_2305_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_vars_2311_);
v___x_2314_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
v_code_2254_ = v_k_2303_;
v_a_2255_ = v___x_2314_;
goto _start;
}
}
else
{
lean_dec(v_fvarId_2308_);
lean_del_object(v___x_2305_);
lean_dec_ref(v_k_2303_);
lean_dec_ref(v_a_2255_);
return v___x_2309_;
}
}
else
{
lean_del_object(v___x_2305_);
lean_dec_ref(v_k_2303_);
lean_dec_ref(v_decl_2302_);
lean_dec_ref(v_a_2255_);
return v___x_2307_;
}
}
}
case 3:
{
lean_object* v_fvarId_2318_; lean_object* v_args_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2376_; 
lean_del_object(v___x_2266_);
v_fvarId_2318_ = lean_ctor_get(v_code_2254_, 0);
v_args_2319_ = lean_ctor_get(v_code_2254_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_code_2254_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2321_ = v_code_2254_;
v_isShared_2322_ = v_isSharedCheck_2376_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_args_2319_);
lean_inc(v_fvarId_2318_);
lean_dec(v_code_2254_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2376_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___x_2333_; 
lean_inc(v_fvarId_2318_);
v___x_2333_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(v_fvarId_2318_, v_a_2255_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2374_; 
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v___x_2333_, 0);
lean_dec(v_unused_2375_);
v___x_2335_ = v___x_2333_;
v_isShared_2336_ = v_isSharedCheck_2374_;
goto v_resetjp_2334_;
}
else
{
lean_dec(v___x_2333_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2374_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
uint8_t v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = 0;
lean_inc(v_fvarId_2318_);
v___x_2338_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_2337_, v_fvarId_2318_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(v_a_2339_);
v___x_2341_ = lean_array_get_size(v_args_2319_);
v___x_2342_ = lean_nat_dec_eq(v___x_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_object* v_binderName_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v_binderName_2343_ = lean_ctor_get(v_a_2339_, 1);
lean_inc(v_binderName_2343_);
lean_dec(v_a_2339_);
v___x_2344_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_check___closed__2, &l_Lean_Compiler_LCNF_Check_Pure_check___closed__2_once, _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__2);
v___x_2345_ = l_Lean_MessageData_ofName(v_binderName_2343_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 7);
lean_ctor_set(v___x_2321_, 1, v___x_2345_);
lean_ctor_set(v___x_2321_, 0, v___x_2344_);
v___x_2347_ = v___x_2321_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2348_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_check___closed__4, &l_Lean_Compiler_LCNF_Check_Pure_check___closed__4_once, _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__4);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = l_Nat_reprFast(v___x_2340_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 3);
lean_ctor_set(v___x_2335_, 0, v___x_2350_);
v___x_2352_ = v___x_2335_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2353_ = l_Lean_MessageData_ofFormat(v___x_2352_);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2349_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_check___closed__6, &l_Lean_Compiler_LCNF_Check_Pure_check___closed__6_once, _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__6);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = l_Nat_reprFast(v___x_2341_);
v___x_2358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
v___x_2359_ = l_Lean_MessageData_ofFormat(v___x_2358_);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2356_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_check___closed__8, &l_Lean_Compiler_LCNF_Check_Pure_check___closed__8_once, _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__8);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_2362_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_dec_ref_known(v___x_2363_, 1);
v___y_2324_ = v_a_2255_;
v___y_2325_ = v_a_2256_;
v___y_2326_ = v_a_2257_;
v___y_2327_ = v_a_2258_;
v___y_2328_ = v_a_2259_;
v___y_2329_ = v_a_2260_;
v___y_2330_ = v_a_2261_;
goto v___jp_2323_;
}
else
{
lean_dec_ref(v_args_2319_);
lean_dec(v_fvarId_2318_);
lean_dec_ref(v_a_2255_);
return v___x_2363_;
}
}
}
}
else
{
lean_dec(v___x_2340_);
lean_dec(v_a_2339_);
lean_del_object(v___x_2335_);
lean_del_object(v___x_2321_);
v___y_2324_ = v_a_2255_;
v___y_2325_ = v_a_2256_;
v___y_2326_ = v_a_2257_;
v___y_2327_ = v_a_2258_;
v___y_2328_ = v_a_2259_;
v___y_2329_ = v_a_2260_;
v___y_2330_ = v_a_2261_;
goto v___jp_2323_;
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_del_object(v___x_2335_);
lean_del_object(v___x_2321_);
lean_dec_ref(v_args_2319_);
lean_dec(v_fvarId_2318_);
lean_dec_ref(v_a_2255_);
v_a_2366_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2338_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2338_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
else
{
lean_del_object(v___x_2321_);
lean_dec_ref(v_args_2319_);
lean_dec(v_fvarId_2318_);
lean_dec_ref(v_a_2255_);
return v___x_2333_;
}
v___jp_2323_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = l_Lean_Expr_fvar___override(v_fvarId_2318_);
v___x_2332_ = l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(v___x_2331_, v_args_2319_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec_ref(v___y_2324_);
return v___x_2332_;
}
}
}
case 4:
{
lean_object* v_cases_2377_; lean_object* v___x_2378_; 
lean_del_object(v___x_2266_);
v_cases_2377_ = lean_ctor_get(v_code_2254_, 0);
lean_inc_ref(v_cases_2377_);
lean_dec_ref_known(v_code_2254_, 1);
v___x_2378_ = l_Lean_Compiler_LCNF_Check_Pure_checkCases(v_cases_2377_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_a_2255_);
return v___x_2378_;
}
case 5:
{
lean_object* v_fvarId_2379_; lean_object* v___x_2380_; 
lean_del_object(v___x_2266_);
v_fvarId_2379_ = lean_ctor_get(v_code_2254_, 0);
lean_inc(v_fvarId_2379_);
lean_dec_ref_known(v_code_2254_, 1);
v___x_2380_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(v_fvarId_2379_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_a_2255_);
return v___x_2380_;
}
default: 
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_dec_ref_known(v_code_2254_, 1);
lean_dec_ref(v_a_2255_);
v___x_2381_ = lean_box(0);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2381_);
v___x_2383_ = v___x_2266_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_2255_);
lean_dec_ref(v_code_2254_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(lean_object* v_value_2387_, lean_object* v___x_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Compiler_LCNF_Check_Pure_check(v_value_2387_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; 
v_unused_2405_ = lean_ctor_get(v___x_2397_, 0);
lean_dec(v_unused_2405_);
v___x_2399_ = v___x_2397_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_dec(v___x_2397_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2388_);
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2388_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
else
{
return v___x_2397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0___boxed(lean_object* v_value_2406_, lean_object* v___x_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(v_value_2406_, v___x_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkCases___boxed(lean_object* v_c_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Compiler_LCNF_Check_Pure_checkCases(v_c_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___boxed(lean_object* v_funDecl_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(v_funDecl_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_check___boxed(lean_object* v_code_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Compiler_LCNF_Check_Pure_check(v_code_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed(lean_object* v_declName_2447_, lean_object* v_params_2448_, lean_object* v_type_2449_, lean_object* v_value_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(v_declName_2447_, v_params_2448_, v_type_2449_, v_value_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___boxed(lean_object* v_typeName_2460_, lean_object* v_as_2461_, lean_object* v_sz_2462_, lean_object* v_i_2463_, lean_object* v_b_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
size_t v_sz_boxed_2473_; size_t v_i_boxed_2474_; lean_object* v_res_2475_; 
v_sz_boxed_2473_ = lean_unbox_usize(v_sz_2462_);
lean_dec(v_sz_2462_);
v_i_boxed_2474_ = lean_unbox_usize(v_i_2463_);
lean_dec(v_i_2463_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(v_typeName_2460_, v_as_2461_, v_sz_boxed_2473_, v_i_boxed_2474_, v_b_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec_ref(v_as_2461_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(lean_object* v_as_2476_, size_t v_i_2477_, size_t v_stop_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_as_2476_, v_i_2477_, v_stop_2478_, v_b_2479_, v___y_2481_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___boxed(lean_object* v_as_2489_, lean_object* v_i_2490_, lean_object* v_stop_2491_, lean_object* v_b_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
size_t v_i_boxed_2501_; size_t v_stop_boxed_2502_; lean_object* v_res_2503_; 
v_i_boxed_2501_ = lean_unbox_usize(v_i_2490_);
lean_dec(v_i_2490_);
v_stop_boxed_2502_ = lean_unbox_usize(v_stop_2491_);
lean_dec(v_stop_2491_);
v_res_2503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(v_as_2489_, v_i_boxed_2501_, v_stop_boxed_2502_, v_b_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v_as_2489_);
return v_res_2503_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = lean_unsigned_to_nat(32u);
v___x_2507_ = lean_mk_empty_array_with_capacity(v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2(void){
_start:
{
size_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2509_ = ((size_t)5ULL);
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = lean_unsigned_to_nat(32u);
v___x_2512_ = lean_mk_empty_array_with_capacity(v___x_2511_);
v___x_2513_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1, &l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1);
v___x_2514_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set(v___x_2514_, 1, v___x_2512_);
lean_ctor_set(v___x_2514_, 2, v___x_2510_);
lean_ctor_set(v___x_2514_, 3, v___x_2510_);
lean_ctor_set_usize(v___x_2514_, 4, v___x_2509_);
return v___x_2514_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3, &l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2518_ = lean_box(1);
v___x_2519_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2, &l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2);
v___x_2520_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__4, &l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__4);
v___x_2521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___x_2519_);
lean_ctor_set(v___x_2521_, 2, v___x_2518_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg(lean_object* v_x_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2528_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_2529_ = ((lean_object*)(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0));
v___x_2530_ = lean_st_mk_ref(v___x_2528_);
v___x_2531_ = lean_obj_once(&l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__5, &l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__5);
lean_inc(v_a_2526_);
lean_inc_ref(v_a_2525_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v___x_2530_);
v___x_2532_ = lean_apply_8(v_x_2522_, v___x_2529_, v___x_2530_, v___x_2531_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, lean_box(0));
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2541_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2537_ = lean_st_ref_get(v___x_2530_);
lean_dec(v___x_2530_);
lean_dec(v___x_2537_);
if (v_isShared_2536_ == 0)
{
v___x_2539_ = v___x_2535_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2533_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_dec(v___x_2530_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___redArg___boxed(lean_object* v_x_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(v_x_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_run(lean_object* v_00_u03b1_2549_, lean_object* v_x_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(v_x_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_Pure_run___boxed(lean_object* v_00_u03b1_2557_, lean_object* v_x_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_Compiler_LCNF_Check_Pure_run(v_00_u03b1_2557_, v_x_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(lean_object* v_f_2565_, lean_object* v_v_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
if (lean_obj_tag(v_v_2566_) == 0)
{
lean_object* v_code_2575_; lean_object* v___x_2576_; 
v_code_2575_ = lean_ctor_get(v_v_2566_, 0);
lean_inc_ref(v_code_2575_);
lean_dec_ref_known(v_v_2566_, 1);
lean_inc(v___y_2573_);
lean_inc_ref(v___y_2572_);
lean_inc(v___y_2571_);
lean_inc_ref(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc(v___y_2568_);
lean_inc_ref(v___y_2567_);
v___x_2576_ = lean_apply_9(v_f_2565_, v_code_2575_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, lean_box(0));
return v___x_2576_;
}
else
{
lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v_f_2565_);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_v_2566_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v_v_2566_, 0);
lean_dec(v_unused_2585_);
v___x_2578_ = v_v_2566_;
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
else
{
lean_dec(v_v_2566_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_box(0);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2580_);
v___x_2582_ = v___x_2578_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg___boxed(lean_object* v_f_2586_, lean_object* v_v_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(v_f_2586_, v_v_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0(uint8_t v_pu_2597_, lean_object* v_f_2598_, lean_object* v_v_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(v_f_2598_, v_v_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed(lean_object* v_pu_2609_, lean_object* v_f_2610_, lean_object* v_v_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v_pu_boxed_2620_; lean_object* v_res_2621_; 
v_pu_boxed_2620_ = lean_unbox(v_pu_2609_);
v_res_2621_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0(v_pu_boxed_2620_, v_f_2610_, v_v_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_check(uint8_t v_pu_2622_, lean_object* v_decl_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
if (v_pu_2622_ == 0)
{
lean_object* v_toSignature_2629_; lean_object* v_value_2630_; lean_object* v_name_2631_; lean_object* v_type_2632_; lean_object* v_params_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_toSignature_2629_ = lean_ctor_get(v_decl_2623_, 0);
lean_inc_ref(v_toSignature_2629_);
v_value_2630_ = lean_ctor_get(v_decl_2623_, 1);
lean_inc_ref(v_value_2630_);
lean_dec_ref(v_decl_2623_);
v_name_2631_ = lean_ctor_get(v_toSignature_2629_, 0);
lean_inc(v_name_2631_);
v_type_2632_ = lean_ctor_get(v_toSignature_2629_, 2);
lean_inc_ref(v_type_2632_);
v_params_2633_ = lean_ctor_get(v_toSignature_2629_, 3);
lean_inc_ref(v_params_2633_);
lean_dec_ref(v_toSignature_2629_);
v___x_2634_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed), 12, 3);
lean_closure_set(v___x_2634_, 0, v_name_2631_);
lean_closure_set(v___x_2634_, 1, v_params_2633_);
lean_closure_set(v___x_2634_, 2, v_type_2632_);
v___x_2635_ = lean_box(v_pu_2622_);
v___x_2636_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed), 11, 3);
lean_closure_set(v___x_2636_, 0, v___x_2635_);
lean_closure_set(v___x_2636_, 1, v___x_2634_);
lean_closure_set(v___x_2636_, 2, v_value_2630_);
v___x_2637_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(v___x_2636_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
return v___x_2637_;
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec_ref(v_decl_2623_);
v___x_2638_ = lean_box(0);
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_check___boxed(lean_object* v_pu_2640_, lean_object* v_decl_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
uint8_t v_pu_boxed_2647_; lean_object* v_res_2648_; 
v_pu_boxed_2647_ = lean_unbox(v_pu_2640_);
v_res_2648_ = l_Lean_Compiler_LCNF_Decl_check(v_pu_boxed_2647_, v_decl_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
return v_res_2648_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InductiveOverride(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Check(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InductiveOverride(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Check(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InductiveOverride(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Check(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InductiveOverride(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Check(builtin);
}
#ifdef __cplusplus
}
#endif
