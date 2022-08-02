// Lean compiler output
// Module: Lean.Meta.Eval
// Imports: Init Lean.Meta.Check
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
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_evalExprCore___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_evalExprCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___at_Lean_Meta_evalExprCore___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addAndCompile___at_Lean_Meta_evalExprCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_evalExprCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_evalExprCore___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr___rarg___lambda__1___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14(lean_object*);
static lean_object* l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___rarg___closed__2;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Meta_evalExpr___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15(lean_object*);
static lean_object* l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
static lean_object* l_Lean_Meta_evalExprCore___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__2;
static lean_object* l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1(lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_compileDecl(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_evalExprCore___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_KernelException_toMessageData(x_1, x_7);
x_9 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_259; uint8_t x_260; 
x_259 = 2;
x_260 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(x_3, x_259);
if (x_260 == 0)
{
lean_object* x_261; 
x_261 = lean_box(0);
x_9 = x_261;
goto block_258;
}
else
{
uint8_t x_262; 
lean_inc(x_2);
x_262 = l_Lean_MessageData_hasSyntheticSorry(x_2);
if (x_262 == 0)
{
lean_object* x_263; 
x_263 = lean_box(0);
x_9 = x_263;
goto block_258;
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_2);
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_8);
return x_265;
}
}
block_258:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_ctor_get(x_6, 6);
x_14 = lean_ctor_get(x_6, 7);
x_15 = l_Lean_replaceRef(x_1, x_12);
x_16 = 0;
x_17 = l_Lean_Syntax_getPos_x3f(x_15, x_16);
x_18 = l_Lean_Syntax_getTailPos_x3f(x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_19 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_FileMap_toPosition(x_11, x_22);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_14);
lean_inc(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_14);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_27 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
lean_inc(x_10);
x_28 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_3);
x_29 = lean_st_ref_take(x_7, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_30, 5);
x_34 = l_Std_PersistentArray_push___rarg(x_33, x_28);
lean_ctor_set(x_30, 5, x_34);
x_35 = lean_st_ref_set(x_7, x_30, x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
x_44 = lean_ctor_get(x_30, 2);
x_45 = lean_ctor_get(x_30, 3);
x_46 = lean_ctor_get(x_30, 4);
x_47 = lean_ctor_get(x_30, 5);
x_48 = lean_ctor_get(x_30, 6);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_49 = l_Std_PersistentArray_push___rarg(x_47, x_28);
x_50 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_49);
lean_ctor_set(x_50, 6, x_48);
x_51 = lean_st_ref_set(x_7, x_50, x_31);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_18);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_57 = lean_ctor_get(x_18, 0);
x_58 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_FileMap_toPosition(x_11, x_61);
x_63 = l_Lean_FileMap_toPosition(x_11, x_57);
lean_dec(x_57);
lean_ctor_set(x_18, 0, x_63);
lean_inc(x_14);
lean_inc(x_13);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_13);
lean_ctor_set(x_64, 1, x_14);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
x_66 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
lean_inc(x_10);
x_67 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_67, 0, x_10);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_18);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_67, 4, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*5, x_3);
x_68 = lean_st_ref_take(x_7, x_60);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_69, 5);
x_73 = l_Std_PersistentArray_push___rarg(x_72, x_67);
lean_ctor_set(x_69, 5, x_73);
x_74 = lean_st_ref_set(x_7, x_69, x_70);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get(x_69, 0);
x_82 = lean_ctor_get(x_69, 1);
x_83 = lean_ctor_get(x_69, 2);
x_84 = lean_ctor_get(x_69, 3);
x_85 = lean_ctor_get(x_69, 4);
x_86 = lean_ctor_get(x_69, 5);
x_87 = lean_ctor_get(x_69, 6);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_69);
x_88 = l_Std_PersistentArray_push___rarg(x_86, x_67);
x_89 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_83);
lean_ctor_set(x_89, 3, x_84);
lean_ctor_set(x_89, 4, x_85);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set(x_89, 6, x_87);
x_90 = lean_st_ref_set(x_7, x_89, x_70);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_95 = lean_ctor_get(x_18, 0);
lean_inc(x_95);
lean_dec(x_18);
x_96 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_FileMap_toPosition(x_11, x_99);
x_101 = l_Lean_FileMap_toPosition(x_11, x_95);
lean_dec(x_95);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
lean_inc(x_14);
lean_inc(x_13);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_13);
lean_ctor_set(x_103, 1, x_14);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_97);
x_105 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
lean_inc(x_10);
x_106 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_106, 0, x_10);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_102);
lean_ctor_set(x_106, 3, x_105);
lean_ctor_set(x_106, 4, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*5, x_3);
x_107 = lean_st_ref_take(x_7, x_98);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 6);
lean_inc(x_116);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 lean_ctor_release(x_108, 5);
 lean_ctor_release(x_108, 6);
 x_117 = x_108;
} else {
 lean_dec_ref(x_108);
 x_117 = lean_box(0);
}
x_118 = l_Std_PersistentArray_push___rarg(x_115, x_106);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 7, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_110);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_119, 2, x_112);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set(x_119, 4, x_114);
lean_ctor_set(x_119, 5, x_118);
lean_ctor_set(x_119, 6, x_116);
x_120 = lean_st_ref_set(x_7, x_119, x_109);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_17);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_126 = lean_ctor_get(x_17, 0);
x_127 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_FileMap_toPosition(x_11, x_126);
lean_dec(x_126);
lean_inc(x_130);
lean_ctor_set(x_17, 0, x_130);
lean_inc(x_14);
lean_inc(x_13);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_13);
lean_ctor_set(x_131, 1, x_14);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_128);
x_133 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
lean_inc(x_10);
x_134 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_134, 0, x_10);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set(x_134, 2, x_17);
lean_ctor_set(x_134, 3, x_133);
lean_ctor_set(x_134, 4, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*5, x_3);
x_135 = lean_st_ref_take(x_7, x_129);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = !lean_is_exclusive(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_136, 5);
x_140 = l_Std_PersistentArray_push___rarg(x_139, x_134);
lean_ctor_set(x_136, 5, x_140);
x_141 = lean_st_ref_set(x_7, x_136, x_137);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 0);
lean_dec(x_143);
x_144 = lean_box(0);
lean_ctor_set(x_141, 0, x_144);
return x_141;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_148 = lean_ctor_get(x_136, 0);
x_149 = lean_ctor_get(x_136, 1);
x_150 = lean_ctor_get(x_136, 2);
x_151 = lean_ctor_get(x_136, 3);
x_152 = lean_ctor_get(x_136, 4);
x_153 = lean_ctor_get(x_136, 5);
x_154 = lean_ctor_get(x_136, 6);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_136);
x_155 = l_Std_PersistentArray_push___rarg(x_153, x_134);
x_156 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_156, 0, x_148);
lean_ctor_set(x_156, 1, x_149);
lean_ctor_set(x_156, 2, x_150);
lean_ctor_set(x_156, 3, x_151);
lean_ctor_set(x_156, 4, x_152);
lean_ctor_set(x_156, 5, x_155);
lean_ctor_set(x_156, 6, x_154);
x_157 = lean_st_ref_set(x_7, x_156, x_137);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_162 = lean_ctor_get(x_17, 0);
lean_inc(x_162);
lean_dec(x_17);
x_163 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_FileMap_toPosition(x_11, x_162);
lean_dec(x_162);
lean_inc(x_166);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
lean_inc(x_14);
lean_inc(x_13);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_13);
lean_ctor_set(x_168, 1, x_14);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_164);
x_170 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
lean_inc(x_10);
x_171 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_171, 0, x_10);
lean_ctor_set(x_171, 1, x_166);
lean_ctor_set(x_171, 2, x_167);
lean_ctor_set(x_171, 3, x_170);
lean_ctor_set(x_171, 4, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*5, x_3);
x_172 = lean_st_ref_take(x_7, x_165);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_173, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_173, 5);
lean_inc(x_180);
x_181 = lean_ctor_get(x_173, 6);
lean_inc(x_181);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 lean_ctor_release(x_173, 3);
 lean_ctor_release(x_173, 4);
 lean_ctor_release(x_173, 5);
 lean_ctor_release(x_173, 6);
 x_182 = x_173;
} else {
 lean_dec_ref(x_173);
 x_182 = lean_box(0);
}
x_183 = l_Std_PersistentArray_push___rarg(x_180, x_171);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 7, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_175);
lean_ctor_set(x_184, 1, x_176);
lean_ctor_set(x_184, 2, x_177);
lean_ctor_set(x_184, 3, x_178);
lean_ctor_set(x_184, 4, x_179);
lean_ctor_set(x_184, 5, x_183);
lean_ctor_set(x_184, 6, x_181);
x_185 = lean_st_ref_set(x_7, x_184, x_174);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
x_188 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_17, 0);
lean_inc(x_190);
lean_dec(x_17);
x_191 = !lean_is_exclusive(x_18);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_192 = lean_ctor_get(x_18, 0);
x_193 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_FileMap_toPosition(x_11, x_190);
lean_dec(x_190);
x_197 = l_Lean_FileMap_toPosition(x_11, x_192);
lean_dec(x_192);
lean_ctor_set(x_18, 0, x_197);
lean_inc(x_14);
lean_inc(x_13);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_13);
lean_ctor_set(x_198, 1, x_14);
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_194);
x_200 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
lean_inc(x_10);
x_201 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_201, 0, x_10);
lean_ctor_set(x_201, 1, x_196);
lean_ctor_set(x_201, 2, x_18);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*5, x_3);
x_202 = lean_st_ref_take(x_7, x_195);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = !lean_is_exclusive(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_206 = lean_ctor_get(x_203, 5);
x_207 = l_Std_PersistentArray_push___rarg(x_206, x_201);
lean_ctor_set(x_203, 5, x_207);
x_208 = lean_st_ref_set(x_7, x_203, x_204);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_208, 0);
lean_dec(x_210);
x_211 = lean_box(0);
lean_ctor_set(x_208, 0, x_211);
return x_208;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_208, 1);
lean_inc(x_212);
lean_dec(x_208);
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_215 = lean_ctor_get(x_203, 0);
x_216 = lean_ctor_get(x_203, 1);
x_217 = lean_ctor_get(x_203, 2);
x_218 = lean_ctor_get(x_203, 3);
x_219 = lean_ctor_get(x_203, 4);
x_220 = lean_ctor_get(x_203, 5);
x_221 = lean_ctor_get(x_203, 6);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_203);
x_222 = l_Std_PersistentArray_push___rarg(x_220, x_201);
x_223 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_223, 0, x_215);
lean_ctor_set(x_223, 1, x_216);
lean_ctor_set(x_223, 2, x_217);
lean_ctor_set(x_223, 3, x_218);
lean_ctor_set(x_223, 4, x_219);
lean_ctor_set(x_223, 5, x_222);
lean_ctor_set(x_223, 6, x_221);
x_224 = lean_st_ref_set(x_7, x_223, x_204);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = lean_box(0);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_229 = lean_ctor_get(x_18, 0);
lean_inc(x_229);
lean_dec(x_18);
x_230 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = l_Lean_FileMap_toPosition(x_11, x_190);
lean_dec(x_190);
x_234 = l_Lean_FileMap_toPosition(x_11, x_229);
lean_dec(x_229);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_234);
lean_inc(x_14);
lean_inc(x_13);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_13);
lean_ctor_set(x_236, 1, x_14);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_231);
x_238 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
lean_inc(x_10);
x_239 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_239, 0, x_10);
lean_ctor_set(x_239, 1, x_233);
lean_ctor_set(x_239, 2, x_235);
lean_ctor_set(x_239, 3, x_238);
lean_ctor_set(x_239, 4, x_237);
lean_ctor_set_uint8(x_239, sizeof(void*)*5, x_3);
x_240 = lean_st_ref_take(x_7, x_232);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_241, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_241, 4);
lean_inc(x_247);
x_248 = lean_ctor_get(x_241, 5);
lean_inc(x_248);
x_249 = lean_ctor_get(x_241, 6);
lean_inc(x_249);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 lean_ctor_release(x_241, 4);
 lean_ctor_release(x_241, 5);
 lean_ctor_release(x_241, 6);
 x_250 = x_241;
} else {
 lean_dec_ref(x_241);
 x_250 = lean_box(0);
}
x_251 = l_Std_PersistentArray_push___rarg(x_248, x_239);
if (lean_is_scalar(x_250)) {
 x_252 = lean_alloc_ctor(0, 7, 0);
} else {
 x_252 = x_250;
}
lean_ctor_set(x_252, 0, x_243);
lean_ctor_set(x_252, 1, x_244);
lean_ctor_set(x_252, 2, x_245);
lean_ctor_set(x_252, 3, x_246);
lean_ctor_set(x_252, 4, x_247);
lean_ctor_set(x_252, 5, x_251);
lean_ctor_set(x_252, 6, x_249);
x_253 = lean_st_ref_set(x_7, x_252, x_242);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
x_256 = lean_box(0);
if (lean_is_scalar(x_255)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_255;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_254);
return x_257;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_evalExprCore___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
x_9 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4___closed__1;
x_9 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_log___at_Lean_Meta_evalExprCore___spec__5(x_1, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; 
x_12 = 2;
x_13 = l_Lean_log___at_Lean_Meta_evalExprCore___spec__5(x_1, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_add_decl(x_11, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3(x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_15, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration uses 'sorry'", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 5);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___lambda__1(x_1, x_14, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__3;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4(x_16, x_2, x_3, x_4, x_5, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___lambda__1(x_1, x_18, x_2, x_3, x_4, x_5, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___lambda__1(x_1, x_21, x_2, x_3, x_4, x_5, x_9);
return x_22;
}
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_is_aux_recursor(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_3);
x_5 = l_Lean_isRecCore(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_8 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_7, x_3);
lean_dec(x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
else
{
uint8_t x_11; 
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_isCasesOnRecursor(x_1, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_13 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_12, x_3);
lean_dec(x_3);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_inc(x_3);
x_16 = l_Lean_isRecCore(x_1, x_3);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = 0;
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_19 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_18, x_3);
lean_dec(x_3);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = 0;
return x_22;
}
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code generator does not support recursor '", 42);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' yet, consider using 'match ... with' and/or structural recursion", 66);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_33 = lean_ctor_get(x_10, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_1);
x_35 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_35, 0, x_1);
x_36 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_35, x_34);
if (lean_obj_tag(x_36) == 0)
{
x_12 = x_8;
goto block_32;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 4)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_43, x_4, x_5, x_6, x_7, x_8);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_dec(x_37);
x_12 = x_8;
goto block_32;
}
}
block_32:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
x_2 = x_16;
x_3 = x_11;
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_24, x_4, x_5, x_6, x_7, x_12);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_18);
x_30 = lean_box(0);
x_2 = x_30;
x_3 = x_11;
x_8 = x_12;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
x_2 = x_15;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_23, x_4, x_5, x_6, x_7, x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_17);
x_29 = lean_box(0);
x_2 = x_29;
x_3 = x_11;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_22, 0, x_1);
x_23 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_22, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 2);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_box(0);
lean_inc(x_1);
x_26 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__11(x_1, x_25, x_24, x_4, x_5, x_6, x_7, x_8);
x_12 = x_26;
goto block_20;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
if (lean_obj_tag(x_27) == 4)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_33, x_4, x_5, x_6, x_7, x_8);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
x_12 = x_34;
goto block_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_12 = x_38;
goto block_20;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_27);
x_39 = lean_ctor_get(x_10, 2);
lean_inc(x_39);
lean_dec(x_10);
x_40 = lean_box(0);
lean_inc(x_1);
x_41 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__11(x_1, x_40, x_39, x_4, x_5, x_6, x_7, x_8);
x_12 = x_41;
goto block_20;
}
}
block_20:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_2 = x_13;
x_3 = x_11;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_evalExprCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_12, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_22, x_4, x_5, x_6, x_7, x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_1);
x_46 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_46, 0, x_1);
x_47 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_46, x_29);
if (lean_obj_tag(x_47) == 0)
{
x_30 = x_8;
goto block_45;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 4)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_28);
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_54, x_4, x_5, x_6, x_7, x_8);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_dec(x_48);
x_30 = x_8;
goto block_45;
}
}
block_45:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_1);
x_32 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_31, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
if (lean_obj_tag(x_35) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_41, x_4, x_5, x_6, x_7, x_30);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_30);
return x_44;
}
}
}
}
case 2:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_80; lean_object* x_81; 
lean_dec(x_3);
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 2);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_1);
x_80 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_80, 0, x_1);
x_81 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_80, x_63);
if (lean_obj_tag(x_81) == 0)
{
x_64 = x_8;
goto block_79;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 4)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_62);
lean_dec(x_1);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_88, x_4, x_5, x_6, x_7, x_8);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_dec(x_82);
x_64 = x_8;
goto block_79;
}
}
block_79:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_65, 0, x_1);
x_66 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_65, x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
if (lean_obj_tag(x_69) == 4)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_75, x_4, x_5, x_6, x_7, x_64);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_69);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_64);
return x_78;
}
}
}
}
case 3:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_114; lean_object* x_115; 
lean_dec(x_3);
x_94 = lean_ctor_get(x_2, 0);
lean_inc(x_94);
lean_dec(x_2);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 2);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_1);
x_114 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_114, 0, x_1);
x_115 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_114, x_97);
if (lean_obj_tag(x_115) == 0)
{
x_98 = x_8;
goto block_113;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 4)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_96);
lean_dec(x_1);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_122, x_4, x_5, x_6, x_7, x_8);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
return x_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_123);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
else
{
lean_dec(x_116);
x_98 = x_8;
goto block_113;
}
}
block_113:
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed), 2, 1);
lean_closure_set(x_99, 0, x_1);
x_100 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_99, x_96);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
lean_dec(x_100);
if (lean_obj_tag(x_103) == 4)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_109, x_4, x_5, x_6, x_7, x_98);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_103);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_98);
return x_112;
}
}
}
}
case 4:
{
lean_object* x_128; 
lean_dec(x_1);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_3);
lean_ctor_set(x_128, 1, x_8);
return x_128;
}
case 5:
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_2, 0);
lean_inc(x_129);
lean_dec(x_2);
x_130 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10(x_1, x_3, x_129, x_4, x_5, x_6, x_7, x_8);
return x_130;
}
default: 
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_2, 2);
lean_inc(x_131);
lean_dec(x_2);
x_132 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__12(x_1, x_3, x_131, x_4, x_5, x_6, x_7, x_8);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_evalExprCore___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l_Lean_Declaration_foldExprM___at_Lean_Meta_evalExprCore___spec__9(x_10, x_1, x_11, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___at_Lean_Meta_evalExprCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
lean_inc(x_1);
x_12 = l_Lean_Environment_compileDecl(x_10, x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 11)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_evalExprCore___spec__8(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_18, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3(x_13, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_25, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___at_Lean_Meta_evalExprCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_compileDecl___at_Lean_Meta_evalExprCore___spec__7(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_eval_const(x_10, x_11, x_1);
lean_dec(x_1);
lean_dec(x_10);
x_13 = l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14___rarg(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_tmp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_evalExprCore___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_evalExprCore___rarg___closed__2;
x_14 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_13, x_6, x_7, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_18);
x_20 = lean_apply_6(x_2, x_18, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
lean_inc(x_15);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_18);
lean_inc(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_3);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_addAndCompile___at_Lean_Meta_evalExprCore___spec__1(x_27, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13___rarg(x_15, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_12, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_12, x_4, x_5, x_6, x_7, x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_15);
x_45 = lean_ctor_get(x_28, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_dec(x_28);
x_47 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_12, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_1);
x_52 = lean_ctor_get(x_20, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_dec(x_20);
x_54 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_12, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_17, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_dec(x_17);
x_61 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_12, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_evalExprCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_log___at_Lean_Meta_evalExprCore___spec__5(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_evalExprCore___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_evalExprCore___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_evalExprCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Declaration_foldExprM___at_Lean_Meta_evalExprCore___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_evalExprCore___spec__15___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExcept___at_Lean_Meta_evalExprCore___spec__14___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_evalExprCore___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected type at evalExpr", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnfD(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isConstOf(x_10, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_8);
x_13 = l_Lean_indentExpr(x_10);
x_14 = l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_17, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Lean_Expr_isConstOf(x_20, x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_indentExpr(x_20);
x_24 = l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_27, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_evalExprCore___rarg(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_evalExpr_x27___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_evalExpr_x27___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected type at `evalExpr` ", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExpr___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_8 = l_Lean_Meta_isExprDefEq(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_2, x_1, x_3, x_4, x_5, x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_evalExpr___rarg___lambda__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_18, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_8, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___rarg___lambda__1), 7, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_evalExprCore___rarg(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_evalExpr___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1 = _init_l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_evalExprCore___spec__6___closed__1);
l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4___closed__1 = _init_l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4___closed__1();
lean_mark_persistent(l_Lean_logWarning___at_Lean_Meta_evalExprCore___spec__4___closed__1);
l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__1 = _init_l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__1();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__1);
l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__2 = _init_l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__2();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__2);
l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__3 = _init_l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__3();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2___closed__3);
l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__1 = _init_l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__1);
l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2 = _init_l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__2);
l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__3 = _init_l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__3();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__3);
l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4 = _init_l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_evalExprCore___spec__10___closed__4);
l_Lean_Meta_evalExprCore___rarg___closed__1 = _init_l_Lean_Meta_evalExprCore___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_evalExprCore___rarg___closed__1);
l_Lean_Meta_evalExprCore___rarg___closed__2 = _init_l_Lean_Meta_evalExprCore___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_evalExprCore___rarg___closed__2);
l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__1);
l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__2);
l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__3 = _init_l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_evalExpr_x27___rarg___lambda__1___closed__3);
l_Lean_Meta_evalExpr___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_evalExpr___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_evalExpr___rarg___lambda__1___closed__1);
l_Lean_Meta_evalExpr___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_evalExpr___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_evalExpr___rarg___lambda__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
