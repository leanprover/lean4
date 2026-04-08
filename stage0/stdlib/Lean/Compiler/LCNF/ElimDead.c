// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: public import Lean.Compiler.LCNF.PassManager
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
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elimDeadVars"};
static const lean_object* l_Lean_Compiler_LCNF_elimDeadVars___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 0, 81, 239, 85, 207, 93, 43)}};
static const lean_object* l_Lean_Compiler_LCNF_elimDeadVars___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 243, 129, 181, 154, 70, 99, 130)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ElimDead"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 82, 16, 255, 163, 142, 141, 196)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 8, 203, 14, 95, 80, 254, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 234, 121, 60, 250, 43, 214, 104)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 227, 118, 194, 153, 141, 66, 82)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 98, 178, 120, 48, 202, 193, 105)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 72, 106, 172, 157, 167, 211, 99)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(154, 254, 227, 186, 107, 229, 199, 236)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 208, 60, 24, 36, 96, 26, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 167, 57, 206, 2, 48, 8, 63)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 61, 197, 124, 13, 119, 183, 129)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 167, 154, 33, 100, 235, 233, 237)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(792928910) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(49, 145, 23, 34, 28, 29, 91, 149)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 85, 234, 87, 122, 159, 213, 105)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 221, 1, 151, 193, 161, 193, 61)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(79, 252, 64, 212, 189, 9, 17, 216)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v___x_6_ = l_Lean_instBEqFVarId_beq(v_key_4_, v_a_1_);
if (v___x_6_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
return v_x_12_;
}
else
{
lean_object* v_key_14_; lean_object* v_value_15_; lean_object* v_tail_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_39_; 
v_key_14_ = lean_ctor_get(v_x_13_, 0);
v_value_15_ = lean_ctor_get(v_x_13_, 1);
v_tail_16_ = lean_ctor_get(v_x_13_, 2);
v_isSharedCheck_39_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_39_ == 0)
{
v___x_18_ = v_x_13_;
v_isShared_19_ = v_isSharedCheck_39_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_tail_16_);
lean_inc(v_value_15_);
lean_inc(v_key_14_);
lean_dec(v_x_13_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_39_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v_fold_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_20_ = lean_array_get_size(v_x_12_);
v___x_21_ = l_Lean_instHashableFVarId_hash(v_key_14_);
v___x_22_ = 32ULL;
v___x_23_ = lean_uint64_shift_right(v___x_21_, v___x_22_);
v_fold_24_ = lean_uint64_xor(v___x_21_, v___x_23_);
v___x_25_ = 16ULL;
v___x_26_ = lean_uint64_shift_right(v_fold_24_, v___x_25_);
v___x_27_ = lean_uint64_xor(v_fold_24_, v___x_26_);
v___x_28_ = lean_uint64_to_usize(v___x_27_);
v___x_29_ = lean_usize_of_nat(v___x_20_);
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_sub(v___x_29_, v___x_30_);
v___x_32_ = lean_usize_land(v___x_28_, v___x_31_);
v___x_33_ = lean_array_uget_borrowed(v_x_12_, v___x_32_);
lean_inc(v___x_33_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 2, v___x_33_);
v___x_35_ = v___x_18_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_key_14_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_value_15_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v___x_33_);
v___x_35_ = v_reuseFailAlloc_38_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; 
v___x_36_ = lean_array_uset(v_x_12_, v___x_32_, v___x_35_);
v_x_12_ = v___x_36_;
v_x_13_ = v_tail_16_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(lean_object* v_i_40_, lean_object* v_source_41_, lean_object* v_target_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_array_get_size(v_source_41_);
v___x_44_ = lean_nat_dec_lt(v_i_40_, v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v_source_41_);
lean_dec(v_i_40_);
return v_target_42_;
}
else
{
lean_object* v_es_45_; lean_object* v___x_46_; lean_object* v_source_47_; lean_object* v_target_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_es_45_ = lean_array_fget(v_source_41_, v_i_40_);
v___x_46_ = lean_box(0);
v_source_47_ = lean_array_fset(v_source_41_, v_i_40_, v___x_46_);
v_target_48_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(v_target_42_, v_es_45_);
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_i_40_, v___x_49_);
lean_dec(v_i_40_);
v_i_40_ = v___x_50_;
v_source_41_ = v_source_47_;
v_target_42_ = v_target_48_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(lean_object* v_data_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_nbuckets_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_53_ = lean_array_get_size(v_data_52_);
v___x_54_ = lean_unsigned_to_nat(2u);
v_nbuckets_55_ = lean_nat_mul(v___x_53_, v___x_54_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_box(0);
v___x_58_ = lean_mk_array(v_nbuckets_55_, v___x_57_);
v___x_59_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(v___x_56_, v_data_52_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(lean_object* v_m_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
lean_object* v_size_63_; lean_object* v_buckets_64_; lean_object* v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v_fold_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; lean_object* v_bkt_78_; uint8_t v___x_79_; 
v_size_63_ = lean_ctor_get(v_m_60_, 0);
v_buckets_64_ = lean_ctor_get(v_m_60_, 1);
v___x_65_ = lean_array_get_size(v_buckets_64_);
v___x_66_ = l_Lean_instHashableFVarId_hash(v_a_61_);
v___x_67_ = 32ULL;
v___x_68_ = lean_uint64_shift_right(v___x_66_, v___x_67_);
v_fold_69_ = lean_uint64_xor(v___x_66_, v___x_68_);
v___x_70_ = 16ULL;
v___x_71_ = lean_uint64_shift_right(v_fold_69_, v___x_70_);
v___x_72_ = lean_uint64_xor(v_fold_69_, v___x_71_);
v___x_73_ = lean_uint64_to_usize(v___x_72_);
v___x_74_ = lean_usize_of_nat(v___x_65_);
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_sub(v___x_74_, v___x_75_);
v___x_77_ = lean_usize_land(v___x_73_, v___x_76_);
v_bkt_78_ = lean_array_uget_borrowed(v_buckets_64_, v___x_77_);
v___x_79_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_61_, v_bkt_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_100_; 
lean_inc_ref(v_buckets_64_);
lean_inc(v_size_63_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_m_60_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_101_ = lean_ctor_get(v_m_60_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_m_60_, 0);
lean_dec(v_unused_102_);
v___x_81_ = v_m_60_;
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_m_60_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v_size_x27_84_; lean_object* v___x_85_; lean_object* v_buckets_x27_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v_size_x27_84_ = lean_nat_add(v_size_63_, v___x_83_);
lean_dec(v_size_63_);
lean_inc(v_bkt_78_);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v_a_61_);
lean_ctor_set(v___x_85_, 1, v_b_62_);
lean_ctor_set(v___x_85_, 2, v_bkt_78_);
v_buckets_x27_86_ = lean_array_uset(v_buckets_64_, v___x_77_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(4u);
v___x_88_ = lean_nat_mul(v_size_x27_84_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_div(v___x_88_, v___x_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_array_get_size(v_buckets_x27_86_);
v___x_92_ = lean_nat_dec_le(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v_val_93_; lean_object* v___x_95_; 
v_val_93_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(v_buckets_x27_86_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_val_93_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_95_ = v___x_81_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_val_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_buckets_x27_86_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_98_ = v___x_81_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_buckets_x27_86_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_dec(v_b_62_);
lean_dec(v_a_61_);
return v_m_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(lean_object* v_s_103_, lean_object* v_arg_104_){
_start:
{
if (lean_obj_tag(v_arg_104_) == 1)
{
lean_object* v_fvarId_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_fvarId_105_ = lean_ctor_get(v_arg_104_, 0);
lean_inc(v_fvarId_105_);
lean_dec_ref(v_arg_104_);
v___x_106_ = lean_box(0);
v___x_107_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_103_, v_fvarId_105_, v___x_106_);
return v___x_107_;
}
else
{
lean_dec(v_arg_104_);
return v_s_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(uint8_t v_pu_108_, lean_object* v_s_109_, lean_object* v_arg_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_s_109_, v_arg_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object* v_pu_112_, lean_object* v_s_113_, lean_object* v_arg_114_){
_start:
{
uint8_t v_pu_boxed_115_; lean_object* v_res_116_; 
v_pu_boxed_115_ = lean_unbox(v_pu_112_);
v_res_116_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(v_pu_boxed_115_, v_s_113_, v_arg_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0(lean_object* v_00_u03b2_117_, lean_object* v_m_118_, lean_object* v_a_119_, lean_object* v_b_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_m_118_, v_a_119_, v_b_120_);
return v___x_121_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0(lean_object* v_00_u03b2_122_, lean_object* v_a_123_, lean_object* v_x_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_123_, v_x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___boxed(lean_object* v_00_u03b2_126_, lean_object* v_a_127_, lean_object* v_x_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0(v_00_u03b2_126_, v_a_127_, v_x_128_);
lean_dec(v_x_128_);
lean_dec(v_a_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1(lean_object* v_00_u03b2_131_, lean_object* v_data_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(v_data_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_134_, lean_object* v_i_135_, lean_object* v_source_136_, lean_object* v_target_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(v_i_135_, v_source_136_, v_target_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(v_x_140_, v_x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(lean_object* v_as_143_, size_t v_i_144_, size_t v_stop_145_, lean_object* v_b_146_){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = lean_usize_dec_eq(v_i_144_, v_stop_145_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; size_t v___x_150_; size_t v___x_151_; 
v___x_148_ = lean_array_uget_borrowed(v_as_143_, v_i_144_);
lean_inc(v___x_148_);
v___x_149_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_b_146_, v___x_148_);
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_add(v_i_144_, v___x_150_);
v_i_144_ = v___x_151_;
v_b_146_ = v___x_149_;
goto _start;
}
else
{
return v_b_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg___boxed(lean_object* v_as_153_, lean_object* v_i_154_, lean_object* v_stop_155_, lean_object* v_b_156_){
_start:
{
size_t v_i_boxed_157_; size_t v_stop_boxed_158_; lean_object* v_res_159_; 
v_i_boxed_157_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_stop_boxed_158_ = lean_unbox_usize(v_stop_155_);
lean_dec(v_stop_155_);
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_153_, v_i_boxed_157_, v_stop_boxed_158_, v_b_156_);
lean_dec_ref(v_as_153_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(uint8_t v_pu_160_, lean_object* v_s_161_, lean_object* v_args_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_array_get_size(v_args_162_);
v___x_165_ = lean_nat_dec_lt(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
return v_s_161_;
}
else
{
uint8_t v___x_166_; 
v___x_166_ = lean_nat_dec_le(v___x_164_, v___x_164_);
if (v___x_166_ == 0)
{
if (v___x_165_ == 0)
{
return v_s_161_;
}
else
{
size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((size_t)0ULL);
v___x_168_ = lean_usize_of_nat(v___x_164_);
v___x_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_162_, v___x_167_, v___x_168_, v_s_161_);
return v___x_169_;
}
}
else
{
size_t v___x_170_; size_t v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((size_t)0ULL);
v___x_171_ = lean_usize_of_nat(v___x_164_);
v___x_172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_162_, v___x_170_, v___x_171_, v_s_161_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object* v_pu_173_, lean_object* v_s_174_, lean_object* v_args_175_){
_start:
{
uint8_t v_pu_boxed_176_; lean_object* v_res_177_; 
v_pu_boxed_176_ = lean_unbox(v_pu_173_);
v_res_177_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_boxed_176_, v_s_174_, v_args_175_);
lean_dec_ref(v_args_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(uint8_t v_pu_178_, lean_object* v_as_179_, size_t v_i_180_, size_t v_stop_181_, lean_object* v_b_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_179_, v_i_180_, v_stop_181_, v_b_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object* v_pu_184_, lean_object* v_as_185_, lean_object* v_i_186_, lean_object* v_stop_187_, lean_object* v_b_188_){
_start:
{
uint8_t v_pu_boxed_189_; size_t v_i_boxed_190_; size_t v_stop_boxed_191_; lean_object* v_res_192_; 
v_pu_boxed_189_ = lean_unbox(v_pu_184_);
v_i_boxed_190_ = lean_unbox_usize(v_i_186_);
lean_dec(v_i_186_);
v_stop_boxed_191_ = lean_unbox_usize(v_stop_187_);
lean_dec(v_stop_187_);
v_res_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(v_pu_boxed_189_, v_as_185_, v_i_boxed_190_, v_stop_boxed_191_, v_b_188_);
lean_dec_ref(v_as_185_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(uint8_t v_pu_193_, lean_object* v_s_194_, lean_object* v_e_195_){
_start:
{
lean_object* v_fvarId_197_; lean_object* v_fvarId_201_; 
switch(lean_obj_tag(v_e_195_))
{
case 2:
{
lean_object* v_struct_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_struct_204_ = lean_ctor_get(v_e_195_, 2);
lean_inc(v_struct_204_);
lean_dec_ref(v_e_195_);
v___x_205_ = lean_box(0);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_194_, v_struct_204_, v___x_205_);
return v___x_206_;
}
case 3:
{
lean_object* v_args_207_; lean_object* v___x_208_; 
v_args_207_ = lean_ctor_get(v_e_195_, 2);
lean_inc_ref(v_args_207_);
lean_dec_ref(v_e_195_);
v___x_208_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_193_, v_s_194_, v_args_207_);
lean_dec_ref(v_args_207_);
return v___x_208_;
}
case 4:
{
lean_object* v_fvarId_209_; lean_object* v_args_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_fvarId_209_ = lean_ctor_get(v_e_195_, 0);
lean_inc(v_fvarId_209_);
v_args_210_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_args_210_);
lean_dec_ref(v_e_195_);
v___x_211_ = lean_box(0);
v___x_212_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_194_, v_fvarId_209_, v___x_211_);
v___x_213_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_193_, v___x_212_, v_args_210_);
lean_dec_ref(v_args_210_);
return v___x_213_;
}
case 5:
{
lean_object* v_args_214_; lean_object* v___x_215_; 
v_args_214_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_args_214_);
lean_dec_ref(v_e_195_);
v___x_215_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_193_, v_s_194_, v_args_214_);
lean_dec_ref(v_args_214_);
return v___x_215_;
}
case 6:
{
lean_object* v_var_216_; 
v_var_216_ = lean_ctor_get(v_e_195_, 1);
lean_inc(v_var_216_);
lean_dec_ref(v_e_195_);
v_fvarId_201_ = v_var_216_;
goto v___jp_200_;
}
case 7:
{
lean_object* v_var_217_; 
v_var_217_ = lean_ctor_get(v_e_195_, 1);
lean_inc(v_var_217_);
lean_dec_ref(v_e_195_);
v_fvarId_201_ = v_var_217_;
goto v___jp_200_;
}
case 8:
{
lean_object* v_var_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_var_218_ = lean_ctor_get(v_e_195_, 2);
lean_inc(v_var_218_);
lean_dec_ref(v_e_195_);
v___x_219_ = lean_box(0);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_194_, v_var_218_, v___x_219_);
return v___x_220_;
}
case 9:
{
lean_object* v_args_221_; lean_object* v___x_222_; 
v_args_221_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_args_221_);
lean_dec_ref(v_e_195_);
v___x_222_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_193_, v_s_194_, v_args_221_);
lean_dec_ref(v_args_221_);
return v___x_222_;
}
case 10:
{
lean_object* v_args_223_; lean_object* v___x_224_; 
v_args_223_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_args_223_);
lean_dec_ref(v_e_195_);
v___x_224_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_193_, v_s_194_, v_args_223_);
lean_dec_ref(v_args_223_);
return v___x_224_;
}
case 11:
{
lean_object* v_var_225_; 
v_var_225_ = lean_ctor_get(v_e_195_, 1);
lean_inc(v_var_225_);
lean_dec_ref(v_e_195_);
v_fvarId_201_ = v_var_225_;
goto v___jp_200_;
}
case 12:
{
lean_object* v_var_226_; lean_object* v_args_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_var_226_ = lean_ctor_get(v_e_195_, 0);
lean_inc(v_var_226_);
v_args_227_ = lean_ctor_get(v_e_195_, 2);
lean_inc_ref(v_args_227_);
lean_dec_ref(v_e_195_);
v___x_228_ = lean_box(0);
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_194_, v_var_226_, v___x_228_);
v___x_230_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_193_, v___x_229_, v_args_227_);
lean_dec_ref(v_args_227_);
return v___x_230_;
}
case 13:
{
lean_object* v_fvarId_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_fvarId_231_ = lean_ctor_get(v_e_195_, 1);
lean_inc(v_fvarId_231_);
lean_dec_ref(v_e_195_);
v___x_232_ = lean_box(0);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_194_, v_fvarId_231_, v___x_232_);
return v___x_233_;
}
case 14:
{
lean_object* v_fvarId_234_; 
v_fvarId_234_ = lean_ctor_get(v_e_195_, 0);
lean_inc(v_fvarId_234_);
lean_dec_ref(v_e_195_);
v_fvarId_197_ = v_fvarId_234_;
goto v___jp_196_;
}
case 15:
{
lean_object* v_fvarId_235_; 
v_fvarId_235_ = lean_ctor_get(v_e_195_, 0);
lean_inc(v_fvarId_235_);
lean_dec_ref(v_e_195_);
v_fvarId_197_ = v_fvarId_235_;
goto v___jp_196_;
}
default: 
{
lean_dec(v_e_195_);
return v_s_194_;
}
}
v___jp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_box(0);
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_194_, v_fvarId_197_, v___x_198_);
return v___x_199_;
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_box(0);
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_194_, v_fvarId_201_, v___x_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(lean_object* v_pu_236_, lean_object* v_s_237_, lean_object* v_e_238_){
_start:
{
uint8_t v_pu_boxed_239_; lean_object* v_res_240_; 
v_pu_boxed_239_ = lean_unbox(v_pu_236_);
v_res_240_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_boxed_239_, v_s_237_, v_e_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(lean_object* v_arg_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_244_ = lean_st_ref_take(v_a_242_);
v___x_245_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_244_, v_arg_241_);
v___x_246_ = lean_st_ref_set(v_a_242_, v___x_245_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(lean_object* v_arg_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(v_arg_249_, v_a_250_);
lean_dec(v_a_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(uint8_t v_pu_253_, lean_object* v_arg_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_261_ = lean_st_ref_take(v_a_255_);
v___x_262_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_261_, v_arg_254_);
v___x_263_ = lean_st_ref_set(v_a_255_, v___x_262_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(lean_object* v_pu_266_, lean_object* v_arg_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
uint8_t v_pu_boxed_274_; lean_object* v_res_275_; 
v_pu_boxed_274_ = lean_unbox(v_pu_266_);
v_res_275_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(v_pu_boxed_274_, v_arg_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(uint8_t v_pu_276_, lean_object* v_e_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_280_ = lean_st_ref_take(v_a_278_);
v___x_281_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_276_, v___x_280_, v_e_277_);
v___x_282_ = lean_st_ref_set(v_a_278_, v___x_281_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(lean_object* v_pu_285_, lean_object* v_e_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
uint8_t v_pu_boxed_289_; lean_object* v_res_290_; 
v_pu_boxed_289_ = lean_unbox(v_pu_285_);
v_res_290_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(v_pu_boxed_289_, v_e_286_, v_a_287_);
lean_dec(v_a_287_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(uint8_t v_pu_291_, lean_object* v_e_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_299_ = lean_st_ref_take(v_a_293_);
v___x_300_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_291_, v___x_299_, v_e_292_);
v___x_301_ = lean_st_ref_set(v_a_293_, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(lean_object* v_pu_304_, lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
uint8_t v_pu_boxed_312_; lean_object* v_res_313_; 
v_pu_boxed_312_ = lean_unbox(v_pu_304_);
v_res_313_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(v_pu_boxed_312_, v_e_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(lean_object* v_fvarId_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_319_ = lean_st_ref_take(v_a_317_);
v___x_320_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0));
v___x_321_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1));
v___x_322_ = lean_box(0);
v___x_323_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_320_, v___x_321_, v___x_319_, v_fvarId_316_, v___x_322_);
v___x_324_ = lean_st_ref_set(v_a_317_, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_322_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(lean_object* v_fvarId_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(v_fvarId_326_, v_a_327_);
lean_dec(v_a_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(lean_object* v_fvarId_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_337_ = lean_st_ref_take(v_a_331_);
v___x_338_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0));
v___x_339_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1));
v___x_340_ = lean_box(0);
v___x_341_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_338_, v___x_339_, v___x_337_, v_fvarId_330_, v___x_340_);
v___x_342_ = lean_st_ref_set(v_a_331_, v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(lean_object* v_fvarId_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(v_fvarId_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
return v_res_351_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(uint8_t v_pu_352_, lean_object* v_val_353_){
_start:
{
if (v_pu_352_ == 0)
{
uint8_t v___x_354_; 
v___x_354_ = 1;
return v___x_354_;
}
else
{
switch(lean_obj_tag(v_val_353_))
{
case 1:
{
uint8_t v___x_355_; 
v___x_355_ = 1;
return v___x_355_;
}
case 4:
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
case 9:
{
lean_object* v_args_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_args_357_ = lean_ctor_get(v_val_353_, 1);
v___x_358_ = lean_array_get_size(v_args_357_);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_nat_dec_eq(v___x_358_, v___x_359_);
return v___x_360_;
}
default: 
{
uint8_t v___x_361_; 
v___x_361_ = 1;
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(lean_object* v_pu_362_, lean_object* v_val_363_){
_start:
{
uint8_t v_pu_boxed_364_; uint8_t v_res_365_; lean_object* v_r_366_; 
v_pu_boxed_364_ = lean_unbox(v_pu_362_);
v_res_365_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_boxed_364_, v_val_363_);
lean_dec(v_val_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(lean_object* v_as_367_, size_t v_i_368_, size_t v_stop_369_, lean_object* v_b_370_, lean_object* v___y_371_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_eq(v_i_368_, v_stop_369_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; size_t v___x_379_; size_t v___x_380_; 
v___x_374_ = lean_st_ref_take(v___y_371_);
v___x_375_ = lean_array_uget_borrowed(v_as_367_, v_i_368_);
lean_inc(v___x_375_);
v___x_376_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_374_, v___x_375_);
v___x_377_ = lean_st_ref_set(v___y_371_, v___x_376_);
v___x_378_ = lean_box(0);
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_368_, v___x_379_);
v_i_368_ = v___x_380_;
v_b_370_ = v___x_378_;
goto _start;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_b_370_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(lean_object* v_as_383_, lean_object* v_i_384_, lean_object* v_stop_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
size_t v_i_boxed_389_; size_t v_stop_boxed_390_; lean_object* v_res_391_; 
v_i_boxed_389_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_stop_boxed_390_ = lean_unbox_usize(v_stop_385_);
lean_dec(v_stop_385_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_383_, v_i_boxed_389_, v_stop_boxed_390_, v_b_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v_as_383_);
return v_res_391_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(lean_object* v_m_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_buckets_394_; lean_object* v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v_fold_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; size_t v___x_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_buckets_394_ = lean_ctor_get(v_m_392_, 1);
v___x_395_ = lean_array_get_size(v_buckets_394_);
v___x_396_ = l_Lean_instHashableFVarId_hash(v_a_393_);
v___x_397_ = 32ULL;
v___x_398_ = lean_uint64_shift_right(v___x_396_, v___x_397_);
v_fold_399_ = lean_uint64_xor(v___x_396_, v___x_398_);
v___x_400_ = 16ULL;
v___x_401_ = lean_uint64_shift_right(v_fold_399_, v___x_400_);
v___x_402_ = lean_uint64_xor(v_fold_399_, v___x_401_);
v___x_403_ = lean_uint64_to_usize(v___x_402_);
v___x_404_ = lean_usize_of_nat(v___x_395_);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_sub(v___x_404_, v___x_405_);
v___x_407_ = lean_usize_land(v___x_403_, v___x_406_);
v___x_408_ = lean_array_uget_borrowed(v_buckets_394_, v___x_407_);
v___x_409_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_393_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_m_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_m_410_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(uint8_t v_pu_414_, lean_object* v_i_415_, lean_object* v_as_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_array_get_size(v_as_416_);
v___x_424_ = lean_nat_dec_lt(v_i_415_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_dec(v_i_415_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v_as_416_);
return v___x_425_;
}
else
{
lean_object* v_a_426_; lean_object* v___y_428_; 
v_a_426_ = lean_array_fget_borrowed(v_as_416_, v_i_415_);
switch(lean_obj_tag(v_a_426_))
{
case 0:
{
lean_object* v_code_450_; 
v_code_450_ = lean_ctor_get(v_a_426_, 2);
lean_inc_ref(v_code_450_);
v___y_428_ = v_code_450_;
goto v___jp_427_;
}
case 1:
{
lean_object* v_code_451_; 
v_code_451_ = lean_ctor_get(v_a_426_, 1);
lean_inc_ref(v_code_451_);
v___y_428_ = v_code_451_;
goto v___jp_427_;
}
default: 
{
lean_object* v_code_452_; 
v_code_452_ = lean_ctor_get(v_a_426_, 0);
lean_inc_ref(v_code_452_);
v___y_428_ = v_code_452_;
goto v___jp_427_;
}
}
v___jp_427_:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_414_, v___y_428_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; size_t v___x_432_; size_t v___x_433_; uint8_t v___x_434_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref(v___x_429_);
lean_inc(v_a_426_);
v___x_431_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_426_, v_a_430_);
v___x_432_ = lean_ptr_addr(v_a_426_);
v___x_433_ = lean_ptr_addr(v___x_431_);
v___x_434_ = lean_usize_dec_eq(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_add(v_i_415_, v___x_435_);
v___x_437_ = lean_array_fset(v_as_416_, v_i_415_, v___x_431_);
lean_dec(v_i_415_);
v_i_415_ = v___x_436_;
v_as_416_ = v___x_437_;
goto _start;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v___x_431_);
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_i_415_, v___x_439_);
lean_dec(v_i_415_);
v_i_415_ = v___x_440_;
goto _start;
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v_as_416_);
lean_dec(v_i_415_);
v_a_442_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_429_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_429_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(uint8_t v_pu_453_, lean_object* v_code_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___y_462_; 
switch(lean_obj_tag(v_code_454_))
{
case 0:
{
lean_object* v_decl_479_; lean_object* v_k_480_; lean_object* v___x_481_; 
v_decl_479_ = lean_ctor_get(v_code_454_, 0);
v_k_480_ = lean_ctor_get(v_code_454_, 1);
lean_inc_ref(v_k_480_);
v___x_481_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_480_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_532_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_532_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_532_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_532_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v_fvarId_487_; lean_object* v_value_488_; uint8_t v___y_512_; uint8_t v___x_530_; 
v___x_486_ = lean_st_ref_get(v_a_455_);
v_fvarId_487_ = lean_ctor_get(v_decl_479_, 0);
v_value_488_ = lean_ctor_get(v_decl_479_, 3);
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_486_, v_fvarId_487_);
lean_dec(v___x_486_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; 
v___x_531_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_453_, v_value_488_);
if (v___x_531_ == 0)
{
goto v___jp_489_;
}
else
{
v___y_512_ = v___x_530_;
goto v___jp_511_;
}
}
else
{
v___y_512_ = v___x_530_;
goto v___jp_511_;
}
v___jp_489_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; uint8_t v___x_495_; 
v___x_490_ = lean_st_ref_take(v_a_455_);
lean_inc(v_value_488_);
v___x_491_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_453_, v___x_490_, v_value_488_);
v___x_492_ = lean_st_ref_set(v_a_455_, v___x_491_);
v___x_493_ = lean_ptr_addr(v_k_480_);
v___x_494_ = lean_ptr_addr(v_a_482_);
v___x_495_ = lean_usize_dec_eq(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_505_; 
lean_inc_ref(v_decl_479_);
v_isSharedCheck_505_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; lean_object* v_unused_507_; 
v_unused_506_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_506_);
v_unused_507_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_507_);
v___x_497_ = v_code_454_;
v_isShared_498_ = v_isSharedCheck_505_;
goto v_resetjp_496_;
}
else
{
lean_dec(v_code_454_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_505_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v_a_482_);
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_decl_479_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_a_482_);
v___x_500_ = v_reuseFailAlloc_504_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_500_);
v___x_502_ = v___x_484_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_object* v___x_509_; 
lean_dec(v_a_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_code_454_);
v___x_509_ = v___x_484_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_code_454_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
v___jp_511_:
{
if (v___y_512_ == 0)
{
lean_object* v___x_513_; 
lean_inc_ref(v_decl_479_);
lean_del_object(v___x_484_);
lean_dec_ref(v_code_454_);
v___x_513_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_453_, v_decl_479_, v_a_457_);
lean_dec_ref(v_decl_479_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v___x_513_, 0);
lean_dec(v_unused_521_);
v___x_515_ = v___x_513_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_dec(v___x_513_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v_a_482_);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_482_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_a_482_);
v_a_522_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_513_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_513_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
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
else
{
goto v___jp_489_;
}
}
}
}
else
{
lean_dec_ref(v_code_454_);
return v___x_481_;
}
}
case 1:
{
lean_object* v_decl_533_; lean_object* v_k_534_; lean_object* v___x_535_; 
v_decl_533_ = lean_ctor_get(v_code_454_, 0);
v_k_534_ = lean_ctor_get(v_code_454_, 1);
lean_inc_ref(v_k_534_);
v___x_535_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_534_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; lean_object* v_fvarId_538_; uint8_t v___x_539_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref(v___x_535_);
v___x_537_ = lean_st_ref_get(v_a_455_);
v_fvarId_538_ = lean_ctor_get(v_decl_533_, 0);
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_537_, v_fvarId_538_);
lean_dec(v___x_537_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; lean_object* v___x_541_; 
lean_inc_ref(v_decl_533_);
lean_dec_ref(v_code_454_);
v___x_540_ = 1;
v___x_541_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_453_, v_decl_533_, v___x_540_, v_a_457_);
lean_dec_ref(v_decl_533_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_541_, 0);
lean_dec(v_unused_549_);
v___x_543_ = v___x_541_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_dec(v___x_541_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_a_536_);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_536_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_a_536_);
v_a_550_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_541_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_541_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v___x_558_; 
lean_inc_ref(v_decl_533_);
v___x_558_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_453_, v_decl_533_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_586_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_586_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_586_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_586_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
uint8_t v___y_564_; size_t v___x_580_; size_t v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_ptr_addr(v_k_534_);
v___x_581_ = lean_ptr_addr(v_a_536_);
v___x_582_ = lean_usize_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
v___y_564_ = v___x_582_;
goto v___jp_563_;
}
else
{
size_t v___x_583_; size_t v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_ptr_addr(v_decl_533_);
v___x_584_ = lean_ptr_addr(v_a_559_);
v___x_585_ = lean_usize_dec_eq(v___x_583_, v___x_584_);
v___y_564_ = v___x_585_;
goto v___jp_563_;
}
v___jp_563_:
{
if (v___y_564_ == 0)
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_574_; 
v_isSharedCheck_574_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; lean_object* v_unused_576_; 
v_unused_575_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_576_);
v___x_566_ = v_code_454_;
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_code_454_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v_a_536_);
lean_ctor_set(v___x_566_, 0, v_a_559_);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_a_536_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_569_);
v___x_571_ = v___x_561_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_object* v___x_578_; 
lean_dec(v_a_559_);
lean_dec(v_a_536_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_code_454_);
v___x_578_ = v___x_561_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_code_454_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v_a_536_);
lean_dec_ref(v_code_454_);
v_a_587_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_558_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_558_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_454_);
return v___x_535_;
}
}
case 2:
{
lean_object* v_decl_595_; lean_object* v_k_596_; lean_object* v___x_597_; 
v_decl_595_ = lean_ctor_get(v_code_454_, 0);
v_k_596_ = lean_ctor_get(v_code_454_, 1);
lean_inc_ref(v_k_596_);
v___x_597_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_596_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_599_; lean_object* v_fvarId_600_; uint8_t v___x_601_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v___x_597_);
v___x_599_ = lean_st_ref_get(v_a_455_);
v_fvarId_600_ = lean_ctor_get(v_decl_595_, 0);
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_599_, v_fvarId_600_);
lean_dec(v___x_599_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; lean_object* v___x_603_; 
lean_inc_ref(v_decl_595_);
lean_dec_ref(v_code_454_);
v___x_602_ = 1;
v___x_603_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_453_, v_decl_595_, v___x_602_, v_a_457_);
lean_dec_ref(v_decl_595_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_603_, 0);
lean_dec(v_unused_611_);
v___x_605_ = v___x_603_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_dec(v___x_603_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_a_598_);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_598_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_a_598_);
v_a_612_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_603_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_603_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v___x_620_; 
lean_inc_ref(v_decl_595_);
v___x_620_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_453_, v_decl_595_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_648_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_648_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_648_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_648_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint8_t v___y_626_; size_t v___x_642_; size_t v___x_643_; uint8_t v___x_644_; 
v___x_642_ = lean_ptr_addr(v_k_596_);
v___x_643_ = lean_ptr_addr(v_a_598_);
v___x_644_ = lean_usize_dec_eq(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
v___y_626_ = v___x_644_;
goto v___jp_625_;
}
else
{
size_t v___x_645_; size_t v___x_646_; uint8_t v___x_647_; 
v___x_645_ = lean_ptr_addr(v_decl_595_);
v___x_646_ = lean_ptr_addr(v_a_621_);
v___x_647_ = lean_usize_dec_eq(v___x_645_, v___x_646_);
v___y_626_ = v___x_647_;
goto v___jp_625_;
}
v___jp_625_:
{
if (v___y_626_ == 0)
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_636_; 
v_isSharedCheck_636_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_637_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_638_);
v___x_628_ = v_code_454_;
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
else
{
lean_dec(v_code_454_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_a_598_);
lean_ctor_set(v___x_628_, 0, v_a_621_);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_621_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_a_598_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_631_);
v___x_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v_a_621_);
lean_dec(v_a_598_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_code_454_);
v___x_640_ = v___x_623_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_code_454_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_598_);
lean_dec_ref(v_code_454_);
v_a_649_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_620_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_620_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_454_);
return v___x_597_;
}
}
case 3:
{
lean_object* v_fvarId_657_; lean_object* v_args_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_fvarId_657_ = lean_ctor_get(v_code_454_, 0);
v_args_658_ = lean_ctor_get(v_code_454_, 1);
v___x_659_ = lean_st_ref_take(v_a_455_);
v___x_660_ = lean_box(0);
lean_inc(v_fvarId_657_);
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_659_, v_fvarId_657_, v___x_660_);
v___x_662_ = lean_st_ref_set(v_a_455_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_array_get_size(v_args_658_);
v___x_665_ = lean_nat_dec_lt(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v_code_454_);
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_le(v___x_664_, v___x_664_);
if (v___x_667_ == 0)
{
if (v___x_665_ == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_code_454_);
return v___x_668_;
}
else
{
size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___x_669_ = ((size_t)0ULL);
v___x_670_ = lean_usize_of_nat(v___x_664_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_658_, v___x_669_, v___x_670_, v___x_660_, v_a_455_);
v___y_462_ = v___x_671_;
goto v___jp_461_;
}
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_672_ = ((size_t)0ULL);
v___x_673_ = lean_usize_of_nat(v___x_664_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_658_, v___x_672_, v___x_673_, v___x_660_, v_a_455_);
v___y_462_ = v___x_674_;
goto v___jp_461_;
}
}
}
case 4:
{
lean_object* v_cases_675_; lean_object* v_typeName_676_; lean_object* v_resultType_677_; lean_object* v_discr_678_; lean_object* v_alts_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_722_; 
v_cases_675_ = lean_ctor_get(v_code_454_, 0);
lean_inc_ref(v_cases_675_);
v_typeName_676_ = lean_ctor_get(v_cases_675_, 0);
v_resultType_677_ = lean_ctor_get(v_cases_675_, 1);
v_discr_678_ = lean_ctor_get(v_cases_675_, 2);
v_alts_679_ = lean_ctor_get(v_cases_675_, 3);
v_isSharedCheck_722_ = !lean_is_exclusive(v_cases_675_);
if (v_isSharedCheck_722_ == 0)
{
v___x_681_ = v_cases_675_;
v_isShared_682_ = v_isSharedCheck_722_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_alts_679_);
lean_inc(v_discr_678_);
lean_inc(v_resultType_677_);
lean_inc(v_typeName_676_);
lean_dec(v_cases_675_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_722_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_679_);
v___x_684_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_453_, v___x_683_, v_alts_679_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_713_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_713_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_713_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_713_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; size_t v___x_693_; size_t v___x_694_; uint8_t v___x_695_; 
v___x_689_ = lean_st_ref_take(v_a_455_);
v___x_690_ = lean_box(0);
lean_inc(v_discr_678_);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_689_, v_discr_678_, v___x_690_);
v___x_692_ = lean_st_ref_set(v_a_455_, v___x_691_);
v___x_693_ = lean_ptr_addr(v_alts_679_);
lean_dec_ref(v_alts_679_);
v___x_694_ = lean_ptr_addr(v_a_685_);
v___x_695_ = lean_usize_dec_eq(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_708_; 
v_isSharedCheck_708_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_709_);
v___x_697_ = v_code_454_;
v_isShared_698_ = v_isSharedCheck_708_;
goto v_resetjp_696_;
}
else
{
lean_dec(v_code_454_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_708_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 3, v_a_685_);
v___x_700_ = v___x_681_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_typeName_676_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_resultType_677_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_discr_678_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_a_685_);
v___x_700_ = v_reuseFailAlloc_707_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_702_);
v___x_704_ = v___x_687_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_object* v___x_711_; 
lean_dec(v_a_685_);
lean_del_object(v___x_681_);
lean_dec(v_discr_678_);
lean_dec_ref(v_resultType_677_);
lean_dec(v_typeName_676_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v_code_454_);
v___x_711_ = v___x_687_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_code_454_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_del_object(v___x_681_);
lean_dec_ref(v_alts_679_);
lean_dec(v_discr_678_);
lean_dec_ref(v_resultType_677_);
lean_dec(v_typeName_676_);
lean_dec_ref(v_code_454_);
v_a_714_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_684_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_684_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_fvarId_723_ = lean_ctor_get(v_code_454_, 0);
v___x_724_ = lean_st_ref_take(v_a_455_);
v___x_725_ = lean_box(0);
lean_inc(v_fvarId_723_);
v___x_726_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_724_, v_fvarId_723_, v___x_725_);
v___x_727_ = lean_st_ref_set(v_a_455_, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_code_454_);
return v___x_728_;
}
case 6:
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_code_454_);
return v___x_729_;
}
case 7:
{
lean_object* v_fvarId_730_; lean_object* v_i_731_; lean_object* v_y_732_; lean_object* v_k_733_; lean_object* v___x_734_; 
v_fvarId_730_ = lean_ctor_get(v_code_454_, 0);
v_i_731_ = lean_ctor_get(v_code_454_, 1);
v_y_732_ = lean_ctor_get(v_code_454_, 2);
v_k_733_ = lean_ctor_get(v_code_454_, 3);
lean_inc_ref(v_k_733_);
v___x_734_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_733_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_767_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_767_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_767_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_767_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_st_ref_get(v_a_455_);
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_739_, v_fvarId_730_);
lean_dec(v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_742_; 
lean_dec_ref(v_code_454_);
if (v_isShared_738_ == 0)
{
v___x_742_ = v___x_737_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_735_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; size_t v___x_747_; size_t v___x_748_; uint8_t v___x_749_; 
v___x_744_ = lean_st_ref_take(v_a_455_);
lean_inc(v_y_732_);
v___x_745_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_744_, v_y_732_);
v___x_746_ = lean_st_ref_set(v_a_455_, v___x_745_);
v___x_747_ = lean_ptr_addr(v_k_733_);
v___x_748_ = lean_ptr_addr(v_a_735_);
v___x_749_ = lean_usize_dec_eq(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_759_; 
lean_inc(v_y_732_);
lean_inc(v_i_731_);
lean_inc(v_fvarId_730_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; 
v_unused_760_ = lean_ctor_get(v_code_454_, 3);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_code_454_, 2);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_763_);
v___x_751_ = v_code_454_;
v_isShared_752_ = v_isSharedCheck_759_;
goto v_resetjp_750_;
}
else
{
lean_dec(v_code_454_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_759_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 3, v_a_735_);
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_fvarId_730_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_i_731_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_y_732_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_a_735_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_754_);
v___x_756_ = v___x_737_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v___x_765_; 
lean_dec(v_a_735_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_code_454_);
v___x_765_ = v___x_737_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_code_454_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_454_);
return v___x_734_;
}
}
case 8:
{
lean_object* v_fvarId_768_; lean_object* v_i_769_; lean_object* v_y_770_; lean_object* v_k_771_; lean_object* v___x_772_; 
v_fvarId_768_ = lean_ctor_get(v_code_454_, 0);
v_i_769_ = lean_ctor_get(v_code_454_, 1);
v_y_770_ = lean_ctor_get(v_code_454_, 2);
v_k_771_ = lean_ctor_get(v_code_454_, 3);
lean_inc_ref(v_k_771_);
v___x_772_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_771_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_806_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_806_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_806_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_806_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = lean_st_ref_get(v_a_455_);
v___x_778_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_777_, v_fvarId_768_);
lean_dec(v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v_code_454_);
if (v_isShared_776_ == 0)
{
v___x_780_ = v___x_775_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_773_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; size_t v___x_786_; size_t v___x_787_; uint8_t v___x_788_; 
v___x_782_ = lean_st_ref_take(v_a_455_);
v___x_783_ = lean_box(0);
lean_inc(v_y_770_);
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_782_, v_y_770_, v___x_783_);
v___x_785_ = lean_st_ref_set(v_a_455_, v___x_784_);
v___x_786_ = lean_ptr_addr(v_k_771_);
v___x_787_ = lean_ptr_addr(v_a_773_);
v___x_788_ = lean_usize_dec_eq(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_798_; 
lean_inc(v_y_770_);
lean_inc(v_i_769_);
lean_inc(v_fvarId_768_);
v_isSharedCheck_798_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_799_ = lean_ctor_get(v_code_454_, 3);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_code_454_, 2);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_802_);
v___x_790_ = v_code_454_;
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_code_454_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 3, v_a_773_);
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_fvarId_768_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_i_769_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_y_770_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_a_773_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_793_);
v___x_795_ = v___x_775_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v___x_804_; 
lean_dec(v_a_773_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v_code_454_);
v___x_804_ = v___x_775_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_code_454_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_454_);
return v___x_772_;
}
}
case 9:
{
lean_object* v_fvarId_807_; lean_object* v_i_808_; lean_object* v_offset_809_; lean_object* v_y_810_; lean_object* v_ty_811_; lean_object* v_k_812_; lean_object* v___x_813_; 
v_fvarId_807_ = lean_ctor_get(v_code_454_, 0);
v_i_808_ = lean_ctor_get(v_code_454_, 1);
v_offset_809_ = lean_ctor_get(v_code_454_, 2);
v_y_810_ = lean_ctor_get(v_code_454_, 3);
v_ty_811_ = lean_ctor_get(v_code_454_, 4);
v_k_812_ = lean_ctor_get(v_code_454_, 5);
lean_inc_ref(v_k_812_);
v___x_813_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_812_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_849_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_849_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_849_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_849_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_st_ref_get(v_a_455_);
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_818_, v_fvarId_807_);
lean_dec(v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_821_; 
lean_dec_ref(v_code_454_);
if (v_isShared_817_ == 0)
{
v___x_821_ = v___x_816_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_814_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; size_t v___x_827_; size_t v___x_828_; uint8_t v___x_829_; 
v___x_823_ = lean_st_ref_take(v_a_455_);
v___x_824_ = lean_box(0);
lean_inc(v_y_810_);
v___x_825_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_823_, v_y_810_, v___x_824_);
v___x_826_ = lean_st_ref_set(v_a_455_, v___x_825_);
v___x_827_ = lean_ptr_addr(v_k_812_);
v___x_828_ = lean_ptr_addr(v_a_814_);
v___x_829_ = lean_usize_dec_eq(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_839_; 
lean_inc_ref(v_ty_811_);
lean_inc(v_y_810_);
lean_inc(v_offset_809_);
lean_inc(v_i_808_);
lean_inc(v_fvarId_807_);
v_isSharedCheck_839_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_840_ = lean_ctor_get(v_code_454_, 5);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_code_454_, 4);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_code_454_, 3);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_code_454_, 2);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_845_);
v___x_831_ = v_code_454_;
v_isShared_832_ = v_isSharedCheck_839_;
goto v_resetjp_830_;
}
else
{
lean_dec(v_code_454_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_839_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 5, v_a_814_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_fvarId_807_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_i_808_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_offset_809_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v_y_810_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v_ty_811_);
lean_ctor_set(v_reuseFailAlloc_838_, 5, v_a_814_);
v___x_834_ = v_reuseFailAlloc_838_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_836_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_834_);
v___x_836_ = v___x_816_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v___x_847_; 
lean_dec(v_a_814_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_code_454_);
v___x_847_ = v___x_816_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_code_454_);
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
}
else
{
lean_dec_ref(v_code_454_);
return v___x_813_;
}
}
case 10:
{
lean_object* v_fvarId_850_; lean_object* v_cidx_851_; lean_object* v_k_852_; lean_object* v___x_853_; 
v_fvarId_850_ = lean_ctor_get(v_code_454_, 0);
v_cidx_851_ = lean_ctor_get(v_code_454_, 1);
v_k_852_ = lean_ctor_get(v_code_454_, 2);
lean_inc_ref(v_k_852_);
v___x_853_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_852_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_881_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_881_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_881_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_881_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; uint8_t v___x_864_; 
v___x_858_ = lean_st_ref_take(v_a_455_);
v___x_859_ = lean_box(0);
lean_inc(v_fvarId_850_);
v___x_860_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_858_, v_fvarId_850_, v___x_859_);
v___x_861_ = lean_st_ref_set(v_a_455_, v___x_860_);
v___x_862_ = lean_ptr_addr(v_k_852_);
v___x_863_ = lean_ptr_addr(v_a_854_);
v___x_864_ = lean_usize_dec_eq(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_874_; 
lean_inc(v_cidx_851_);
lean_inc(v_fvarId_850_);
v_isSharedCheck_874_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; lean_object* v_unused_876_; lean_object* v_unused_877_; 
v_unused_875_ = lean_ctor_get(v_code_454_, 2);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_877_);
v___x_866_ = v_code_454_;
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
else
{
lean_dec(v_code_454_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 2, v_a_854_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_fvarId_850_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_cidx_851_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_a_854_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_869_);
v___x_871_ = v___x_856_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v___x_879_; 
lean_dec(v_a_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v_code_454_);
v___x_879_ = v___x_856_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_code_454_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_dec_ref(v_code_454_);
return v___x_853_;
}
}
case 11:
{
lean_object* v_fvarId_882_; lean_object* v_n_883_; uint8_t v_check_884_; uint8_t v_persistent_885_; lean_object* v_k_886_; lean_object* v___x_887_; 
v_fvarId_882_ = lean_ctor_get(v_code_454_, 0);
v_n_883_ = lean_ctor_get(v_code_454_, 1);
v_check_884_ = lean_ctor_get_uint8(v_code_454_, sizeof(void*)*3);
v_persistent_885_ = lean_ctor_get_uint8(v_code_454_, sizeof(void*)*3 + 1);
v_k_886_ = lean_ctor_get(v_code_454_, 2);
lean_inc_ref(v_k_886_);
v___x_887_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_886_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_915_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_915_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_915_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_915_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; size_t v___x_896_; size_t v___x_897_; uint8_t v___x_898_; 
v___x_892_ = lean_st_ref_take(v_a_455_);
v___x_893_ = lean_box(0);
lean_inc(v_fvarId_882_);
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_892_, v_fvarId_882_, v___x_893_);
v___x_895_ = lean_st_ref_set(v_a_455_, v___x_894_);
v___x_896_ = lean_ptr_addr(v_k_886_);
v___x_897_ = lean_ptr_addr(v_a_888_);
v___x_898_ = lean_usize_dec_eq(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_908_; 
lean_inc(v_n_883_);
lean_inc(v_fvarId_882_);
v_isSharedCheck_908_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; 
v_unused_909_ = lean_ctor_get(v_code_454_, 2);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_911_);
v___x_900_ = v_code_454_;
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
else
{
lean_dec(v_code_454_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 2, v_a_888_);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_fvarId_882_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_n_883_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_a_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3, v_check_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3 + 1, v_persistent_885_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_905_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_903_);
v___x_905_ = v___x_890_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
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
else
{
lean_object* v___x_913_; 
lean_dec(v_a_888_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v_code_454_);
v___x_913_ = v___x_890_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_code_454_);
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
lean_dec_ref(v_code_454_);
return v___x_887_;
}
}
case 12:
{
lean_object* v_fvarId_916_; lean_object* v_n_917_; uint8_t v_check_918_; uint8_t v_persistent_919_; lean_object* v_k_920_; lean_object* v___x_921_; 
v_fvarId_916_ = lean_ctor_get(v_code_454_, 0);
v_n_917_ = lean_ctor_get(v_code_454_, 1);
v_check_918_ = lean_ctor_get_uint8(v_code_454_, sizeof(void*)*3);
v_persistent_919_ = lean_ctor_get_uint8(v_code_454_, sizeof(void*)*3 + 1);
v_k_920_ = lean_ctor_get(v_code_454_, 2);
lean_inc_ref(v_k_920_);
v___x_921_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_920_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_949_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_949_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_949_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_949_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; size_t v___x_930_; size_t v___x_931_; uint8_t v___x_932_; 
v___x_926_ = lean_st_ref_take(v_a_455_);
v___x_927_ = lean_box(0);
lean_inc(v_fvarId_916_);
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_926_, v_fvarId_916_, v___x_927_);
v___x_929_ = lean_st_ref_set(v_a_455_, v___x_928_);
v___x_930_ = lean_ptr_addr(v_k_920_);
v___x_931_ = lean_ptr_addr(v_a_922_);
v___x_932_ = lean_usize_dec_eq(v___x_930_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_942_; 
lean_inc(v_n_917_);
lean_inc(v_fvarId_916_);
v_isSharedCheck_942_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; 
v_unused_943_ = lean_ctor_get(v_code_454_, 2);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_945_);
v___x_934_ = v_code_454_;
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
else
{
lean_dec(v_code_454_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 2, v_a_922_);
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_fvarId_916_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_n_917_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_a_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_941_, sizeof(void*)*3, v_check_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_941_, sizeof(void*)*3 + 1, v_persistent_919_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_937_);
v___x_939_ = v___x_924_;
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
lean_object* v___x_947_; 
lean_dec(v_a_922_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_code_454_);
v___x_947_ = v___x_924_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_code_454_);
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
else
{
lean_dec_ref(v_code_454_);
return v___x_921_;
}
}
default: 
{
lean_object* v_fvarId_950_; lean_object* v_k_951_; lean_object* v___x_952_; 
v_fvarId_950_ = lean_ctor_get(v_code_454_, 0);
v_k_951_ = lean_ctor_get(v_code_454_, 1);
lean_inc_ref(v_k_951_);
v___x_952_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_453_, v_k_951_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_979_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_979_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_979_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_979_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; size_t v___x_961_; size_t v___x_962_; uint8_t v___x_963_; 
v___x_957_ = lean_st_ref_take(v_a_455_);
v___x_958_ = lean_box(0);
lean_inc(v_fvarId_950_);
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_957_, v_fvarId_950_, v___x_958_);
v___x_960_ = lean_st_ref_set(v_a_455_, v___x_959_);
v___x_961_ = lean_ptr_addr(v_k_951_);
v___x_962_ = lean_ptr_addr(v_a_953_);
v___x_963_ = lean_usize_dec_eq(v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_973_; 
lean_inc(v_fvarId_950_);
v_isSharedCheck_973_ = !lean_is_exclusive(v_code_454_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_974_ = lean_ctor_get(v_code_454_, 1);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_code_454_, 0);
lean_dec(v_unused_975_);
v___x_965_ = v_code_454_;
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
else
{
lean_dec(v_code_454_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v_a_953_);
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_fvarId_950_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_a_953_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_968_);
v___x_970_ = v___x_955_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v___x_977_; 
lean_dec(v_a_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v_code_454_);
v___x_977_ = v___x_955_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_code_454_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_dec_ref(v_code_454_);
return v___x_952_;
}
}
}
v___jp_461_:
{
if (lean_obj_tag(v___y_462_) == 0)
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_isSharedCheck_469_ = !lean_is_exclusive(v___y_462_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v___y_462_, 0);
lean_dec(v_unused_470_);
v___x_464_ = v___y_462_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_dec(v___y_462_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v_code_454_);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_code_454_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_code_454_);
v_a_471_ = lean_ctor_get(v___y_462_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___y_462_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___y_462_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___y_462_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(uint8_t v_pu_980_, lean_object* v_funDecl_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_params_988_; lean_object* v_type_989_; lean_object* v_value_990_; lean_object* v___x_991_; 
v_params_988_ = lean_ctor_get(v_funDecl_981_, 2);
lean_inc_ref(v_params_988_);
v_type_989_ = lean_ctor_get(v_funDecl_981_, 3);
lean_inc_ref(v_type_989_);
v_value_990_ = lean_ctor_get(v_funDecl_981_, 4);
lean_inc_ref(v_value_990_);
v___x_991_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_980_, v_value_990_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v___x_991_);
v___x_993_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_980_, v_funDecl_981_, v_type_989_, v_params_988_, v_a_992_, v_a_984_);
return v___x_993_;
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v_type_989_);
lean_dec_ref(v_params_988_);
lean_dec_ref(v_funDecl_981_);
v_a_994_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_991_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_991_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(lean_object* v_pu_1002_, lean_object* v_funDecl_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
uint8_t v_pu_boxed_1010_; lean_object* v_res_1011_; 
v_pu_boxed_1010_ = lean_unbox(v_pu_1002_);
v_res_1011_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_boxed_1010_, v_funDecl_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(lean_object* v_pu_1012_, lean_object* v_i_1013_, lean_object* v_as_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
uint8_t v_pu_boxed_1021_; lean_object* v_res_1022_; 
v_pu_boxed_1021_ = lean_unbox(v_pu_1012_);
v_res_1022_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_boxed_1021_, v_i_1013_, v_as_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object* v_pu_1023_, lean_object* v_code_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
uint8_t v_pu_boxed_1031_; lean_object* v_res_1032_; 
v_pu_boxed_1031_ = lean_unbox(v_pu_1023_);
v_res_1032_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_boxed_1031_, v_code_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
return v_res_1032_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_object* v_00_u03b2_1033_, lean_object* v_m_1034_, lean_object* v_a_1035_){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_m_1034_, v_a_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(lean_object* v_00_u03b2_1037_, lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(v_00_u03b2_1037_, v_m_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_m_1038_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(uint8_t v_pu_1042_, lean_object* v_as_1043_, size_t v_i_1044_, size_t v_stop_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_1043_, v_i_1044_, v_stop_1045_, v_b_1046_, v___y_1047_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(lean_object* v_pu_1054_, lean_object* v_as_1055_, lean_object* v_i_1056_, lean_object* v_stop_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v_pu_boxed_1065_; size_t v_i_boxed_1066_; size_t v_stop_boxed_1067_; lean_object* v_res_1068_; 
v_pu_boxed_1065_ = lean_unbox(v_pu_1054_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_stop_boxed_1067_ = lean_unbox_usize(v_stop_1057_);
lean_dec(v_stop_1057_);
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(v_pu_boxed_1065_, v_as_1055_, v_i_boxed_1066_, v_stop_boxed_1067_, v_b_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v_as_1055_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(lean_object* v_f_1069_, lean_object* v_v_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
if (lean_obj_tag(v_v_1070_) == 0)
{
lean_object* v_code_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1100_; 
v_code_1076_ = lean_ctor_get(v_v_1070_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_v_1070_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1078_ = v_v_1070_;
v_isShared_1079_ = v_isSharedCheck_1100_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_code_1076_);
lean_dec(v_v_1070_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1100_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; 
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
lean_inc(v___y_1072_);
lean_inc_ref(v___y_1071_);
v___x_1080_ = lean_apply_6(v_f_1069_, v_code_1076_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, lean_box(0));
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1091_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1091_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1091_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_a_1081_);
v___x_1086_ = v___x_1078_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_del_object(v___x_1078_);
v_a_1092_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1080_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1080_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v___x_1101_; 
lean_dec_ref(v_f_1069_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_v_1070_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(lean_object* v_f_1102_, lean_object* v_v_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_1102_, v_v_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(uint8_t v_pu_1110_, lean_object* v_f_1111_, lean_object* v_v_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_1111_, v_v_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(lean_object* v_pu_1119_, lean_object* v_f_1120_, lean_object* v_v_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v_pu_boxed_1127_; lean_object* v_res_1128_; 
v_pu_boxed_1127_ = lean_unbox(v_pu_1119_);
v_res_1128_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(v_pu_boxed_1127_, v_f_1120_, v_v_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(lean_object* v___x_1129_, uint8_t v_pu_1130_, lean_object* v_code_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_st_mk_ref(v___x_1129_);
v___x_1138_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1130_, v_code_1131_, v___x_1137_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1147_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_st_ref_get(v___x_1137_);
lean_dec(v___x_1137_);
lean_dec(v___x_1143_);
if (v_isShared_1142_ == 0)
{
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1139_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_dec(v___x_1137_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(lean_object* v___x_1148_, lean_object* v_pu_1149_, lean_object* v_code_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v_pu_boxed_1156_; lean_object* v_res_1157_; 
v_pu_boxed_1156_ = lean_unbox(v_pu_1149_);
v_res_1157_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(v___x_1148_, v_pu_boxed_1156_, v_code_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t v_pu_1158_, lean_object* v_decl_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_toSignature_1165_; lean_object* v_value_1166_; uint8_t v_recursive_1167_; lean_object* v_inlineAttr_x3f_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1195_; 
v_toSignature_1165_ = lean_ctor_get(v_decl_1159_, 0);
v_value_1166_ = lean_ctor_get(v_decl_1159_, 1);
v_recursive_1167_ = lean_ctor_get_uint8(v_decl_1159_, sizeof(void*)*3);
v_inlineAttr_x3f_1168_ = lean_ctor_get(v_decl_1159_, 2);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_decl_1159_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1170_ = v_decl_1159_;
v_isShared_1171_ = v_isSharedCheck_1195_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_inlineAttr_x3f_1168_);
lean_inc(v_value_1166_);
lean_inc(v_toSignature_1165_);
lean_dec(v_decl_1159_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1195_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
v___x_1172_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_1173_ = lean_box(v_pu_1158_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1174_, 0, v___x_1172_);
lean_closure_set(v___f_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v___f_1174_, v_value_1166_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1186_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1186_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1186_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_a_1176_);
v___x_1181_ = v___x_1170_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_toSignature_1165_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_a_1176_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_inlineAttr_x3f_1168_);
lean_ctor_set_uint8(v_reuseFailAlloc_1185_, sizeof(void*)*3, v_recursive_1167_);
v___x_1181_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_del_object(v___x_1170_);
lean_dec(v_inlineAttr_x3f_1168_);
lean_dec_ref(v_toSignature_1165_);
v_a_1187_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1175_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1175_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(lean_object* v_pu_1196_, lean_object* v_decl_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
uint8_t v_pu_boxed_1203_; lean_object* v_res_1204_; 
v_pu_boxed_1203_ = lean_unbox(v_pu_1196_);
v_res_1204_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v_pu_boxed_1203_, v_decl_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t v_phase_1208_, lean_object* v_occurrence_1209_){
_start:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1210_ = ((lean_object*)(l_Lean_Compiler_LCNF_elimDeadVars___closed__1));
v___x_1211_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1208_);
v___x_1212_ = lean_box(v___x_1211_);
v___x_1213_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed), 7, 1);
lean_closure_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1210_, v_phase_1208_, v___x_1213_, v_occurrence_1209_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars___boxed(lean_object* v_phase_1215_, lean_object* v_occurrence_1216_){
_start:
{
uint8_t v_phase_boxed_1217_; lean_object* v_res_1218_; 
v_phase_boxed_1217_ = lean_unbox(v_phase_1215_);
v_res_1218_ = l_Lean_Compiler_LCNF_elimDeadVars(v_phase_boxed_1217_, v_occurrence_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1290_ = 1;
v___x_1291_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1292_ = l_Lean_registerTraceClass(v___x_1289_, v___x_1290_, v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
return v_res_1294_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ElimDead(builtin);
}
#ifdef __cplusplus
}
#endif
