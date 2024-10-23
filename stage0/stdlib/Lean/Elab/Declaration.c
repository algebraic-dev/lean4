// Lean compiler output
// Module: Lean.Elab.Declaration
// Imports: Lean.Util.CollectLevelParams Lean.Elab.DeclUtil Lean.Elab.DefView Lean.Elab.Inductive Lean.Elab.Structure Lean.Elab.MutualDef Lean.Elab.DeclarationRange
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
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__22;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__2;
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__1(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__37;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__3;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__8;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__2;
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__3;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__2;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__15;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__2;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3;
lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__5;
lean_object* l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1(lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9;
extern lean_object* l_Lean_declRangeExt;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__1(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4;
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__5;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__1;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__20;
static lean_object* l_Lean_Elab_Command_expandMutualElement___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_expandMutualPreamble___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__13;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__1;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___closed__4;
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7;
extern lean_object* l_Lean_Elab_Term_instMonadTermElabM;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3;
lean_object* l_Lean_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__4;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__7;
static lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__6;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__1;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__17;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabClassInductive___closed__3;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__5;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___closed__5;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__2;
lean_object* l_EStateM_instMonad(lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__4;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__20;
static lean_object* l_Lean_Elab_Command_elabInitialize___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__1;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__2___boxed(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__2;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__6;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__25;
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_withoutCommandIncrementality___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__2;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__2;
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__1;
lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__2(lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__3;
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__30;
static lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___closed__6;
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__5;
lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__1;
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Command_elabAttr___closed__1;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isProtected(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__7;
static lean_object* l_Lean_Elab_Command_elabMutual___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_getDefName_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_findCommon(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__4;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4;
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___closed__5;
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2;
lean_object* l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__38;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2;
lean_object* l_Lean_Elab_addBuiltinIncrementalElab(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_isDefLike(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__5;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_findCommon___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___closed__3;
static lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__4;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__6;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__3;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2;
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__9;
static lean_object* l_Lean_Elab_Command_elabInitialize___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__4;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__4;
lean_object* l_Lean_extractMacroScopes(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__10;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___closed__2;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__2;
extern lean_object* l_Lean_Elab_macroAttribute;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__18;
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__5;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__1;
static lean_object* l_panic___at_Lean_Elab_Command_elabAttr___spec__3___closed__1;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__19;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__1;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMutual___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement__1(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__3;
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__4;
static lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__2;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__10;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__5;
lean_object* l_Lean_MacroScopesView_review(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__3;
lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__39;
static lean_object* l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__15;
static lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__1;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__5;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_object* l_panic___at_Lean_Parser_SyntaxStack_back___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__2;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__6;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__16;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__46;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__3;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___closed__1;
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3;
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3;
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_classInductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___closed__3;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__32;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___boxed(lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandMutualPreamble___closed__3;
static lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___closed__4;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__2;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__11;
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabClassInductive___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__41;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabInitialize__1(lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__11;
static lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMutualDef(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__31;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__6;
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5;
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__8;
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__1;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___closed__7;
static lean_object* l_Lean_Elab_Command_expandMutualPreamble___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace___lambda__1(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
static lean_object* l_Lean_Elab_Command_elabDeclaration___closed__2;
lean_object* l_Lean_Elab_Term_applyAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__1;
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__34;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___closed__1;
lean_object* l_Array_mkArray1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__1;
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
extern lean_object* l_Lean_Linter_linter_deprecated;
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRanges;
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Command_elabAttr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__3;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__11;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__2;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
lean_object* lean_array_mk(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__6;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__6;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__7;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__8;
lean_object* l_List_mapTR_loop___at_Lean_ensureNonAmbiguous___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__2;
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__4;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024_(lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualElement(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___closed__3;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__7;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Command_elabClassInductive___closed__2;
lean_object* l_Array_mkArray2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__1;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMutual___closed__3;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1(lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__21;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3;
static lean_object* l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__27;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__45;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__3;
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__10;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__1;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__17;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6;
static lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__14;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_root_", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid namespace '", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', '_root_' is a reserved namespace", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', it must not contain numeric parts", 36, 36);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_6);
x_11 = 1;
x_12 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2;
x_13 = l_Lean_Name_toString(x_1, x_11, x_12);
x_14 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_Macro_throwError___rarg(x_17, x_2, x_3);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
default: 
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = 1;
x_24 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2;
x_25 = l_Lean_Name_toString(x_1, x_23, x_24);
x_26 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__5;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_Macro_throwError___rarg(x_29, x_2, x_3);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("!(`_root_).isPrefixOf id\n  ", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__2;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Declaration", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.Declaration.0.Lean.Elab.Command.setDeclIdName", 64, 64);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__5;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__6;
x_3 = lean_unsigned_to_nat(30u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_Elab_expandDeclIdCore(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__1;
x_6 = l_Lean_Name_isPrefixOf(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_getHeadInfo(x_1);
x_8 = lean_mk_syntax_ident(x_2);
x_9 = l_Lean_Syntax_setInfo(x_7, x_8);
x_10 = l_Lean_Syntax_isIdent(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_setArg(x_1, x_11, x_9);
return x_12;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__7;
x_14 = l_panic___at_Lean_Parser_SyntaxStack_back___spec__1(x_13);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declaration", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("abbrev", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("theorem", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("opaque", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("axiom", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inductive", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__16;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("classInductive", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__18;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structure", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__20;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__7;
x_9 = lean_name_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
x_11 = lean_name_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__11;
x_13 = lean_name_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13;
x_15 = lean_name_eq(x_7, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__15;
x_17 = lean_name_eq(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__17;
x_19 = lean_name_eq(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__19;
x_21 = lean_name_eq(x_7, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__21;
x_23 = lean_name_eq(x_7, x_22);
lean_dec(x_7);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
x_24 = 1;
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
x_25 = 1;
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
x_26 = 1;
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
x_27 = 1;
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
x_28 = 1;
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
x_29 = 1;
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_7);
x_30 = 1;
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instance", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__2;
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_getDefName_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
lean_dec(x_6);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_Elab_expandDeclIdCore(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
x_15 = lean_box(0);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Syntax_getArg(x_17, x_16);
lean_dec(x_17);
x_19 = l_Lean_Elab_expandDeclIdCore(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("!stx[1][3].isNone\n    ", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__2;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.Declaration.0.Lean.Elab.Command.setDefName", 61, 61);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__5;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__3;
x_3 = lean_unsigned_to_nat(81u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef(x_1);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_8, x_10);
x_12 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName(x_11, x_2);
x_13 = l_Lean_Syntax_setArg(x_8, x_10, x_12);
x_14 = l_Lean_Syntax_setArg(x_6, x_7, x_13);
x_15 = l_Lean_Syntax_setArg(x_1, x_5, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__4;
x_17 = l_panic___at_Lean_Parser_SyntaxStack_back___spec__1(x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_getArg(x_19, x_18);
x_21 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName(x_20, x_2);
x_22 = l_Lean_Syntax_setArg(x_19, x_18, x_21);
x_23 = l_Lean_Syntax_setArg(x_1, x_18, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_extractMacroScopes(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = l_Lean_Name_str___override(x_12, x_11);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
x_18 = l_Lean_MacroScopesView_review(x_17);
x_19 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(x_2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_getDefName_x3f(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__1;
x_9 = l_Lean_Name_isPrefixOf(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lambda__1(x_7, x_1, x_10, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l_Lean_Name_replacePrefix(x_7, x_8, x_12);
x_14 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace(x_13, x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 0;
x_7 = l_Lean_Syntax_getPos_x3f(x_1, x_6);
x_8 = l_Lean_Syntax_getTailPos_x3f(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_10 = l_Lean_FileMap_toPosition(x_5, x_9);
lean_inc(x_10);
x_11 = l_Lean_FileMap_leanPosToLspPos(x_5, x_10);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
lean_inc(x_13);
lean_inc(x_10);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
lean_inc(x_16);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
lean_inc(x_5);
x_23 = l_Lean_FileMap_toPosition(x_5, x_22);
lean_dec(x_22);
lean_inc(x_23);
x_24 = l_Lean_FileMap_leanPosToLspPos(x_5, x_23);
lean_dec(x_5);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 0, x_26);
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_dec(x_8);
lean_inc(x_5);
x_29 = l_Lean_FileMap_toPosition(x_5, x_28);
lean_dec(x_28);
lean_inc(x_29);
x_30 = l_Lean_FileMap_leanPosToLspPos(x_5, x_29);
lean_dec(x_5);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_dec(x_7);
lean_inc(x_5);
x_35 = l_Lean_FileMap_toPosition(x_5, x_34);
lean_dec(x_34);
lean_inc(x_35);
x_36 = l_Lean_FileMap_leanPosToLspPos(x_5, x_35);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_37; 
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
lean_inc(x_38);
lean_inc(x_35);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
lean_inc(x_41);
lean_inc(x_35);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_4);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_36, 1);
x_46 = lean_ctor_get(x_36, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
lean_dec(x_8);
lean_inc(x_5);
x_48 = l_Lean_FileMap_toPosition(x_5, x_47);
lean_dec(x_47);
lean_inc(x_48);
x_49 = l_Lean_FileMap_leanPosToLspPos(x_5, x_48);
lean_dec(x_5);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_36, 0, x_51);
return x_36;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_dec(x_36);
x_53 = lean_ctor_get(x_8, 0);
lean_inc(x_53);
lean_dec(x_8);
lean_inc(x_5);
x_54 = l_Lean_FileMap_toPosition(x_5, x_53);
lean_dec(x_53);
lean_inc(x_54);
x_55 = l_Lean_FileMap_leanPosToLspPos(x_5, x_54);
lean_dec(x_5);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_35);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
return x_58;
}
}
}
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_declRangeExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_instInhabitedDeclarationRanges;
x_12 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1;
lean_inc(x_1);
x_13 = l_Lean_MapDeclarationExtension_contains___rarg(x_11, x_12, x_10, x_1);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_14 = lean_st_ref_take(x_4, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = l_Lean_MapDeclarationExtension_insert___rarg(x_12, x_18, x_1, x_2);
lean_ctor_set(x_15, 0, x_19);
x_20 = lean_st_ref_set(x_4, x_15, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
x_29 = lean_ctor_get(x_15, 2);
x_30 = lean_ctor_get(x_15, 3);
x_31 = lean_ctor_get(x_15, 4);
x_32 = lean_ctor_get(x_15, 5);
x_33 = lean_ctor_get(x_15, 6);
x_34 = lean_ctor_get(x_15, 7);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_35 = l_Lean_MapDeclarationExtension_insert___rarg(x_12, x_27, x_1, x_2);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_29);
lean_ctor_set(x_36, 3, x_30);
lean_ctor_set(x_36, 4, x_31);
lean_ctor_set(x_36, 5, x_32);
lean_ctor_set(x_36, 6, x_33);
lean_ctor_set(x_36, 7, x_34);
x_37 = lean_st_ref_set(x_4, x_36, x_16);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
lean_ctor_set(x_6, 0, x_42);
return x_6;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_6);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_instInhabitedDeclarationRanges;
x_47 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1;
lean_inc(x_1);
x_48 = l_Lean_MapDeclarationExtension_contains___rarg(x_46, x_47, x_45, x_1);
lean_dec(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_49 = lean_st_ref_take(x_4, x_44);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 4);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_50, 7);
lean_inc(x_59);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 lean_ctor_release(x_50, 5);
 lean_ctor_release(x_50, 6);
 lean_ctor_release(x_50, 7);
 x_60 = x_50;
} else {
 lean_dec_ref(x_50);
 x_60 = lean_box(0);
}
x_61 = l_Lean_MapDeclarationExtension_insert___rarg(x_47, x_52, x_1, x_2);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 8, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set(x_62, 2, x_54);
lean_ctor_set(x_62, 3, x_55);
lean_ctor_set(x_62, 4, x_56);
lean_ctor_set(x_62, 5, x_57);
lean_ctor_set(x_62, 6, x_58);
lean_ctor_set(x_62, 7, x_59);
x_63 = lean_st_ref_set(x_4, x_62, x_51);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_44);
return x_69;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("example", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
x_6 = l_Lean_Syntax_getKind(x_2);
x_7 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2;
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_3);
x_9 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_2, x_3, x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_getDeclarationSelectionRef(x_2);
lean_inc(x_3);
x_13 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_12, x_3, x_4, x_11);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_13, 1, x_15);
lean_ctor_set(x_13, 0, x_10);
x_17 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(x_1, x_13, x_3, x_4, x_16);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(x_1, x_20, x_3, x_4, x_19);
lean_dec(x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = 1;
x_16 = l_Lean_Elab_Term_addTermInfo_x27(x_2, x_11, x_13, x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_Elab_Term_applyAttributesAt(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_15 = l_Lean_addDecl(x_1, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__1), 9, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
x_18 = l_Lean_Elab_Command_elabAxiom___lambda__3___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_22 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_4, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_11, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_2);
x_28 = l_Lean_isExtern(x_27, x_2);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = 1;
x_30 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_4, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
return x_30;
}
else
{
lean_object* x_31; 
lean_inc(x_11);
lean_inc(x_10);
x_31 = l_Lean_compileDecl(x_1, x_10, x_11, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = 1;
x_34 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_4, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_15, 0);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_15);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__3;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__14;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = 2;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_applyAttributesAt(x_2, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Elab_Term_elabType(x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_26 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_24, x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = 1;
x_33 = 1;
x_34 = l_Lean_Meta_mkForallFVars(x_9, x_30, x_25, x_32, x_33, x_12, x_13, x_14, x_15, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_mkForallFVars(x_4, x_35, x_32, x_32, x_33, x_12, x_13, x_14, x_15, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2;
x_41 = l_Lean_Elab_Term_levelMVarToParam(x_38, x_40, x_10, x_11, x_12, x_13, x_14, x_15, x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__5;
lean_inc(x_43);
x_46 = l_Lean_CollectLevelParams_main(x_43, x_45);
x_47 = lean_ctor_get(x_46, 2);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_sortDeclLevelParams(x_5, x_6, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_free_object(x_41);
lean_dec(x_43);
lean_free_object(x_28);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_ctor_set_tag(x_48, 3);
x_50 = l_Lean_MessageData_ofFormat(x_48);
x_51 = l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(x_7, x_50, x_10, x_11, x_12, x_13, x_14, x_15, x_44);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(x_7, x_54, x_10, x_11, x_12, x_13, x_14, x_15, x_44);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_44);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_inc(x_2);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set(x_62, 2, x_60);
x_63 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_64);
x_65 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7;
x_66 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_65, x_10, x_11, x_12, x_13, x_14, x_15, x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_58);
lean_dec(x_60);
lean_free_object(x_41);
lean_free_object(x_28);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_box(0);
x_71 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_48, x_2, x_8, x_17, x_70, x_10, x_11, x_12, x_13, x_14, x_15, x_69);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_66);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_66, 1);
x_74 = lean_ctor_get(x_66, 0);
lean_dec(x_74);
lean_inc(x_2);
x_75 = l_Lean_MessageData_ofName(x_2);
x_76 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_75);
lean_ctor_set(x_66, 0, x_76);
x_77 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11;
lean_ctor_set_tag(x_58, 7);
lean_ctor_set(x_58, 1, x_77);
lean_ctor_set(x_58, 0, x_66);
x_78 = l_Lean_MessageData_ofExpr(x_60);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_78);
lean_ctor_set(x_41, 0, x_58);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_76);
lean_ctor_set(x_28, 0, x_41);
x_79 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_65, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_73);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_48, x_2, x_8, x_17, x_80, x_10, x_11, x_12, x_13, x_14, x_15, x_81);
lean_dec(x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_dec(x_66);
lean_inc(x_2);
x_84 = l_Lean_MessageData_ofName(x_2);
x_85 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11;
lean_ctor_set_tag(x_58, 7);
lean_ctor_set(x_58, 1, x_87);
lean_ctor_set(x_58, 0, x_86);
x_88 = l_Lean_MessageData_ofExpr(x_60);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_88);
lean_ctor_set(x_41, 0, x_58);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_85);
lean_ctor_set(x_28, 0, x_41);
x_89 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_65, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_83);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_48, x_2, x_8, x_17, x_90, x_10, x_11, x_12, x_13, x_14, x_15, x_91);
lean_dec(x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_93 = lean_ctor_get(x_58, 0);
x_94 = lean_ctor_get(x_58, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_58);
lean_inc(x_93);
lean_inc(x_2);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_57);
lean_ctor_set(x_95, 2, x_93);
x_96 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_dec(x_1);
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_97);
x_98 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7;
x_99 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_98, x_10, x_11, x_12, x_13, x_14, x_15, x_94);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_93);
lean_free_object(x_41);
lean_free_object(x_28);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_box(0);
x_104 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_48, x_2, x_8, x_17, x_103, x_10, x_11, x_12, x_13, x_14, x_15, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
lean_inc(x_2);
x_107 = l_Lean_MessageData_ofName(x_2);
x_108 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_106;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_MessageData_ofExpr(x_93);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_112);
lean_ctor_set(x_41, 0, x_111);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_108);
lean_ctor_set(x_28, 0, x_41);
x_113 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_98, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_105);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_48, x_2, x_8, x_17, x_114, x_10, x_11, x_12, x_13, x_14, x_15, x_115);
lean_dec(x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_117 = lean_ctor_get(x_48, 0);
lean_inc(x_117);
lean_dec(x_48);
x_118 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_44);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
lean_inc(x_119);
lean_inc(x_2);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_2);
lean_ctor_set(x_122, 1, x_117);
lean_ctor_set(x_122, 2, x_119);
x_123 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_dec(x_1);
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7;
x_127 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_126, x_10, x_11, x_12, x_13, x_14, x_15, x_120);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_121);
lean_dec(x_119);
lean_free_object(x_41);
lean_free_object(x_28);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_box(0);
x_132 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_125, x_2, x_8, x_17, x_131, x_10, x_11, x_12, x_13, x_14, x_15, x_130);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
lean_inc(x_2);
x_135 = l_Lean_MessageData_ofName(x_2);
x_136 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(7, 2, 0);
} else {
 x_137 = x_134;
 lean_ctor_set_tag(x_137, 7);
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11;
if (lean_is_scalar(x_121)) {
 x_139 = lean_alloc_ctor(7, 2, 0);
} else {
 x_139 = x_121;
 lean_ctor_set_tag(x_139, 7);
}
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_MessageData_ofExpr(x_119);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_140);
lean_ctor_set(x_41, 0, x_139);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_136);
lean_ctor_set(x_28, 0, x_41);
x_141 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_126, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_133);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_125, x_2, x_8, x_17, x_142, x_10, x_11, x_12, x_13, x_14, x_15, x_143);
lean_dec(x_142);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_41, 0);
x_146 = lean_ctor_get(x_41, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_41);
x_147 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__5;
lean_inc(x_145);
x_148 = l_Lean_CollectLevelParams_main(x_145, x_147);
x_149 = lean_ctor_get(x_148, 2);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_Lean_Elab_sortDeclLevelParams(x_5, x_6, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_145);
lean_free_object(x_28);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(3, 1, 0);
} else {
 x_153 = x_152;
 lean_ctor_set_tag(x_153, 3);
}
lean_ctor_set(x_153, 0, x_151);
x_154 = l_Lean_MessageData_ofFormat(x_153);
x_155 = l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(x_7, x_154, x_10, x_11, x_12, x_13, x_14, x_15, x_146);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_156 = lean_ctor_get(x_150, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_157 = x_150;
} else {
 lean_dec_ref(x_150);
 x_157 = lean_box(0);
}
x_158 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_145, x_10, x_11, x_12, x_13, x_14, x_15, x_146);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
lean_inc(x_159);
lean_inc(x_2);
x_162 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_162, 0, x_2);
lean_ctor_set(x_162, 1, x_156);
lean_ctor_set(x_162, 2, x_159);
x_163 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_dec(x_1);
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(0, 1, 0);
} else {
 x_165 = x_157;
 lean_ctor_set_tag(x_165, 0);
}
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7;
x_167 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_166, x_10, x_11, x_12, x_13, x_14, x_15, x_160);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_161);
lean_dec(x_159);
lean_free_object(x_28);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_box(0);
x_172 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_165, x_2, x_8, x_17, x_171, x_10, x_11, x_12, x_13, x_14, x_15, x_170);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_173 = lean_ctor_get(x_167, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_174 = x_167;
} else {
 lean_dec_ref(x_167);
 x_174 = lean_box(0);
}
lean_inc(x_2);
x_175 = l_Lean_MessageData_ofName(x_2);
x_176 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
if (lean_is_scalar(x_174)) {
 x_177 = lean_alloc_ctor(7, 2, 0);
} else {
 x_177 = x_174;
 lean_ctor_set_tag(x_177, 7);
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11;
if (lean_is_scalar(x_161)) {
 x_179 = lean_alloc_ctor(7, 2, 0);
} else {
 x_179 = x_161;
 lean_ctor_set_tag(x_179, 7);
}
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_MessageData_ofExpr(x_159);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_176);
lean_ctor_set(x_28, 0, x_181);
x_182 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_166, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_173);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_165, x_2, x_8, x_17, x_183, x_10, x_11, x_12, x_13, x_14, x_15, x_184);
lean_dec(x_183);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_free_object(x_28);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_37);
if (x_186 == 0)
{
return x_37;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_37, 0);
x_188 = lean_ctor_get(x_37, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_37);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_free_object(x_28);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_34);
if (x_190 == 0)
{
return x_34;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_34, 0);
x_192 = lean_ctor_get(x_34, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_34);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_28, 0);
x_195 = lean_ctor_get(x_28, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_28);
x_196 = 1;
x_197 = 1;
x_198 = l_Lean_Meta_mkForallFVars(x_9, x_194, x_25, x_196, x_197, x_12, x_13, x_14, x_15, x_195);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_Meta_mkForallFVars(x_4, x_199, x_196, x_196, x_197, x_12, x_13, x_14, x_15, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2;
x_205 = l_Lean_Elab_Term_levelMVarToParam(x_202, x_204, x_10, x_11, x_12, x_13, x_14, x_15, x_203);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__5;
lean_inc(x_206);
x_210 = l_Lean_CollectLevelParams_main(x_206, x_209);
x_211 = lean_ctor_get(x_210, 2);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l_Lean_Elab_sortDeclLevelParams(x_5, x_6, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_208);
lean_dec(x_206);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(3, 1, 0);
} else {
 x_215 = x_214;
 lean_ctor_set_tag(x_215, 3);
}
lean_ctor_set(x_215, 0, x_213);
x_216 = l_Lean_MessageData_ofFormat(x_215);
x_217 = l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(x_7, x_216, x_10, x_11, x_12, x_13, x_14, x_15, x_207);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_218 = lean_ctor_get(x_212, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_219 = x_212;
} else {
 lean_dec_ref(x_212);
 x_219 = lean_box(0);
}
x_220 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_206, x_10, x_11, x_12, x_13, x_14, x_15, x_207);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
lean_inc(x_221);
lean_inc(x_2);
x_224 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_224, 0, x_2);
lean_ctor_set(x_224, 1, x_218);
lean_ctor_set(x_224, 2, x_221);
x_225 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_dec(x_1);
x_226 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set_uint8(x_226, sizeof(void*)*1, x_225);
if (lean_is_scalar(x_219)) {
 x_227 = lean_alloc_ctor(0, 1, 0);
} else {
 x_227 = x_219;
 lean_ctor_set_tag(x_227, 0);
}
lean_ctor_set(x_227, 0, x_226);
x_228 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7;
x_229 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_228, x_10, x_11, x_12, x_13, x_14, x_15, x_222);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_unbox(x_230);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_208);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_box(0);
x_234 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_227, x_2, x_8, x_17, x_233, x_10, x_11, x_12, x_13, x_14, x_15, x_232);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_235 = lean_ctor_get(x_229, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_236 = x_229;
} else {
 lean_dec_ref(x_229);
 x_236 = lean_box(0);
}
lean_inc(x_2);
x_237 = l_Lean_MessageData_ofName(x_2);
x_238 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
if (lean_is_scalar(x_236)) {
 x_239 = lean_alloc_ctor(7, 2, 0);
} else {
 x_239 = x_236;
 lean_ctor_set_tag(x_239, 7);
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_237);
x_240 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11;
if (lean_is_scalar(x_223)) {
 x_241 = lean_alloc_ctor(7, 2, 0);
} else {
 x_241 = x_223;
 lean_ctor_set_tag(x_241, 7);
}
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_Lean_MessageData_ofExpr(x_221);
if (lean_is_scalar(x_208)) {
 x_243 = lean_alloc_ctor(7, 2, 0);
} else {
 x_243 = x_208;
 lean_ctor_set_tag(x_243, 7);
}
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_238);
x_245 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_228, x_244, x_10, x_11, x_12, x_13, x_14, x_15, x_235);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_227, x_2, x_8, x_17, x_246, x_10, x_11, x_12, x_13, x_14, x_15, x_247);
lean_dec(x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_201, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_201, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_251 = x_201;
} else {
 lean_dec_ref(x_201);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_ctor_get(x_198, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_198, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_255 = x_198;
} else {
 lean_dec_ref(x_198);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_26);
if (x_257 == 0)
{
return x_26;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_26, 0);
x_259 = lean_ctor_get(x_26, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_26);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_21);
if (x_261 == 0)
{
return x_21;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_21, 0);
x_263 = lean_ctor_get(x_21, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_21);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_19);
if (x_265 == 0)
{
return x_19;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_19, 0);
x_267 = lean_ctor_get(x_19, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_19);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_Syntax_getArgs(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__4___boxed), 16, 8);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_9);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_7);
lean_closure_set(x_18, 7, x_8);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLevelNames___rarg), 9, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Term_withDeclName___rarg(x_3, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Elab_expandDeclSig(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getLevelNames___rarg(x_4, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_Elab_Command_expandDeclId(x_7, x_1, x_3, x_4, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_19);
x_21 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(x_19, x_2, x_3, x_4, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__5___boxed), 16, 8);
lean_closure_set(x_23, 0, x_11);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_19);
lean_closure_set(x_23, 3, x_12);
lean_closure_set(x_23, 4, x_14);
lean_closure_set(x_23, 5, x_20);
lean_closure_set(x_23, 6, x_2);
lean_closure_set(x_23, 7, x_7);
x_24 = l_Lean_Elab_Command_runTermElabM___rarg(x_23, x_3, x_4, x_22);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabAxiom___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Command_elabAxiom___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Command_elabAxiom___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabAxiom(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid use of attributes in constructor declaration", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2;
x_11 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_10, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid use of 'unsafe' in constructor declaration", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_9, x_3, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid use of 'partial' in constructor declaration", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Elab_Modifiers_isPartial(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_9, x_3, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid use of 'noncomputable' in constructor declaration", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3(x_1, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_8, x_2, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_4);
x_7 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_2, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
x_10 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabAxiom___spec__2(x_3, x_4, x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_ctor_set(x_10, 1, x_12);
lean_ctor_set(x_10, 0, x_8);
x_14 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(x_1, x_10, x_4, x_5, x_13);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3(x_1, x_17, x_4, x_5, x_16);
lean_dec(x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_5);
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1(x_1, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getIdAt(x_2, x_10);
x_12 = l_Lean_Name_append(x_3, x_11);
x_13 = l_Lean_Syntax_getArg(x_2, x_10);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = l_Lean_Elab_Command_getRef(x_5, x_6, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_replaceRef(x_13, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 9);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_29 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set(x_29, 3, x_22);
lean_ctor_set(x_29, 4, x_23);
lean_ctor_set(x_29, 5, x_24);
lean_ctor_set(x_29, 6, x_18);
lean_ctor_set(x_29, 7, x_25);
lean_ctor_set(x_29, 8, x_26);
lean_ctor_set(x_29, 9, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*10, x_28);
x_30 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6(x_14, x_12, x_29, x_6, x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(4u);
x_34 = l_Lean_Syntax_getArg(x_2, x_33);
x_35 = l_Lean_Elab_expandOptDeclSig(x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_inc(x_5);
lean_inc(x_31);
x_39 = l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__13(x_31, x_38, x_5, x_6, x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_31);
x_41 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2(x_31, x_2, x_13, x_5, x_6, x_40);
lean_dec(x_13);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_1);
lean_ctor_set(x_44, 2, x_31);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_37);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_46, 2, x_31);
lean_ctor_set(x_46, 3, x_36);
lean_ctor_set(x_46, 4, x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_30, 0);
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_30);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_8);
if (x_56 == 0)
{
return x_8;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_8, 0);
x_58 = lean_ctor_get(x_8, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_8);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'protected' constructor in a 'private' inductive datatype", 65, 65);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Elab_Modifiers_isProtected(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(x_1, x_2, x_3, x_10, x_6, x_7, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Elab_Modifiers_isPrivate(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(x_1, x_2, x_3, x_13, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2;
x_16 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_15, x_6, x_7, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'private' constructor in a 'private' inductive datatype", 63, 63);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Elab_Modifiers_isPrivate(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(x_4, x_1, x_2, x_3, x_10, x_6, x_7, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Elab_Modifiers_isPrivate(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(x_4, x_1, x_2, x_3, x_13, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__2;
x_16 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_15, x_6, x_7, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_TSyntax_getDocString(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
lean_ctor_set(x_3, 0, x_9);
x_12 = lean_box(0);
x_13 = lean_apply_5(x_2, x_3, x_12, x_5, x_6, x_7);
return x_13;
}
else
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 2, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 3, x_17);
x_20 = lean_box(0);
x_21 = lean_apply_5(x_2, x_19, x_20, x_5, x_6, x_7);
return x_21;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("duplicate doc string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_array_uget(x_5, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_5, x_4, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_11, x_14);
x_16 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_replaceRef(x_11, x_17);
lean_dec(x_17);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
x_28 = lean_ctor_get(x_6, 9);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_30 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_25);
lean_ctor_set(x_30, 6, x_19);
lean_ctor_set(x_30, 7, x_26);
lean_ctor_set(x_30, 8, x_27);
lean_ctor_set(x_30, 9, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*10, x_29);
lean_inc(x_30);
x_31 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_15, x_30, x_7, x_18);
lean_dec(x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_11);
x_34 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___boxed), 8, 3);
lean_closure_set(x_34, 0, x_11);
lean_closure_set(x_34, 1, x_2);
lean_closure_set(x_34, 2, x_1);
x_35 = l_Lean_Syntax_getArg(x_11, x_12);
x_36 = l_Lean_Syntax_getOptional_x3f(x_35);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
x_37 = lean_box(0);
lean_inc(x_2);
x_38 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3(x_11, x_2, x_1, x_32, x_37, x_30, x_7, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
x_42 = lean_usize_add(x_4, x_41);
x_43 = lean_array_uset(x_13, x_4, x_39);
x_4 = x_42;
x_5 = x_43;
x_8 = x_40;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_11);
x_49 = lean_ctor_get(x_32, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 0);
lean_inc(x_50);
lean_dec(x_36);
x_51 = lean_box(0);
lean_inc(x_7);
x_52 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__4(x_50, x_34, x_32, x_51, x_30, x_7, x_33);
lean_dec(x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = 1;
x_56 = lean_usize_add(x_4, x_55);
x_57 = lean_array_uset(x_13, x_4, x_53);
x_4 = x_56;
x_5 = x_57;
x_8 = x_54;
goto _start;
}
else
{
uint8_t x_59; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_49);
x_63 = lean_ctor_get(x_36, 0);
lean_inc(x_63);
lean_dec(x_36);
x_64 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__3;
x_65 = 2;
lean_inc(x_30);
x_66 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_63, x_64, x_65, x_30, x_7, x_33);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_7);
x_69 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__4(x_63, x_34, x_32, x_67, x_30, x_7, x_68);
lean_dec(x_67);
lean_dec(x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = 1;
x_73 = lean_usize_add(x_4, x_72);
x_74 = lean_array_uset(x_13, x_4, x_70);
x_4 = x_73;
x_5 = x_74;
x_8 = x_71;
goto _start;
}
else
{
uint8_t x_76; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_69);
if (x_76 == 0)
{
return x_69;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_69, 0);
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_69);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_31);
if (x_80 == 0)
{
return x_31;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_31, 0);
x_82 = lean_ctor_get(x_31, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_31);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = l_Lean_Syntax_getArg(x_9, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_9, x_13);
x_15 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_9, x_16);
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Syntax_getArg(x_9, x_18);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_19);
x_21 = l_Lean_Elab_Command_getRef(x_4, x_5, x_6);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_25 = lean_array_uset(x_11, x_2, x_20);
x_2 = x_24;
x_3 = x_25;
x_6 = x_22;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("note: this linter can be disabled with `set_option ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" false`", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
lean_inc(x_8);
x_10 = l_Lean_MessageData_ofName(x_8);
x_11 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__2;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_11);
x_12 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__6;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_2, x_20, x_21, x_4, x_5, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_23);
x_24 = l_Lean_MessageData_ofName(x_23);
x_25 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
x_31 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__6;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
x_36 = 1;
x_37 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_2, x_35, x_36, x_4, x_5, x_6);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_instInhabitedScope;
x_13 = l_List_head_x21___rarg(x_12, x_11);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_1);
x_15 = l_Lean_Linter_getLinterValue(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; 
lean_free_object(x_7);
x_17 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6(x_1, x_2, x_3, x_4, x_5, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Command_instInhabitedScope;
x_22 = l_List_head_x21___rarg(x_21, x_20);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_1);
x_24 = l_Lean_Linter_getLinterValue(x_1, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6(x_1, x_2, x_3, x_4, x_5, x_19);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_4);
lean_ctor_set(x_16, 4, x_5);
lean_ctor_set(x_16, 5, x_6);
lean_ctor_set(x_16, 6, x_7);
lean_ctor_set(x_16, 7, x_8);
lean_ctor_set(x_16, 8, x_9);
lean_ctor_set(x_16, 9, x_10);
lean_ctor_set(x_16, 10, x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":=", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'inductive ... :=' has been deprecated in favor of 'inductive ... where'.", 73, 73);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Linter_linter_deprecated;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Elab_Command_checkValidInductiveModifier___at_Lean_Elab_Command_elabStructure___spec__1(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Elab_expandOptDeclSig(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Elab_Command_expandDeclId(x_14, x_1, x_3, x_4, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_19);
x_21 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(x_19, x_2, x_3, x_4, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(4u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_26 = lean_array_size(x_25);
x_27 = 0;
lean_inc(x_4);
lean_inc(x_19);
lean_inc(x_1);
x_28 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3(x_1, x_19, x_26, x_27, x_25, x_3, x_4, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(5u);
x_32 = l_Lean_Syntax_getArg(x_2, x_31);
x_33 = l_Lean_Syntax_getOptional_x3f(x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_80; 
x_80 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4;
x_34 = x_80;
goto block_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_33, 0);
lean_inc(x_81);
lean_dec(x_33);
x_82 = l_Lean_Syntax_getArg(x_81, x_13);
lean_dec(x_81);
x_83 = l_Lean_Syntax_getArgs(x_82);
lean_dec(x_82);
x_34 = x_83;
goto block_79;
}
block_79:
{
size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_array_size(x_34);
x_36 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(x_35, x_27, x_34, x_3, x_4, x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unsigned_to_nat(6u);
x_40 = l_Lean_Syntax_getArg(x_2, x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_getOptDerivingClasses), 4, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = l_Lean_Elab_Command_liftCoreM___rarg(x_41, x_3, x_4, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(3u);
x_46 = l_Lean_Syntax_getArg(x_2, x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Syntax_getArg(x_46, x_47);
x_49 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
x_50 = l_Lean_Syntax_isToken(x_49, x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(x_2, x_14, x_1, x_18, x_19, x_20, x_11, x_12, x_29, x_43, x_37, x_51, x_3, x_4, x_44);
lean_dec(x_4);
lean_dec(x_3);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_53 = l_Lean_Syntax_getArg(x_2, x_47);
x_54 = l_Lean_Elab_Command_getRef(x_3, x_4, x_44);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_replaceRef(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
x_58 = lean_ctor_get(x_3, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_3, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 7);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 8);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 9);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_68 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_62);
lean_ctor_set(x_68, 5, x_63);
lean_ctor_set(x_68, 6, x_57);
lean_ctor_set(x_68, 7, x_64);
lean_ctor_set(x_68, 8, x_65);
lean_ctor_set(x_68, 9, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*10, x_67);
x_69 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__5;
x_70 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__4;
x_71 = l_Lean_Linter_logLintIf___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__5(x_69, x_46, x_70, x_68, x_4, x_56);
lean_dec(x_46);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(x_2, x_14, x_1, x_18, x_19, x_20, x_11, x_12, x_29, x_43, x_37, x_72, x_3, x_4, x_73);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_37);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_42);
if (x_75 == 0)
{
return x_42;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_42, 0);
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_42);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_28);
if (x_84 == 0)
{
return x_28;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_28, 0);
x_86 = lean_ctor_get(x_28, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_28);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_15);
if (x_88 == 0)
{
return x_15;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_15, 0);
x_90 = lean_ctor_get(x_15, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_15);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_6);
if (x_92 == 0)
{
return x_6;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_6, 0);
x_94 = lean_ctor_get(x_6, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_6);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addAuxDeclarationRanges___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__4(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Linter_logLintIf___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_classInductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_mk(x_10);
x_12 = l_Lean_Elab_Command_elabInductiveViews(x_11, x_3, x_4, x_8);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabClassInductive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("class", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabClassInductive___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabClassInductive___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabClassInductive___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Elab_Command_elabClassInductive___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Elab_Command_elabClassInductive___closed__3;
x_7 = l_Lean_Elab_Modifiers_addAttr(x_1, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_mk(x_12);
x_14 = l_Lean_Elab_Command_elabInductiveViews(x_13, x_3, x_4, x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namespace", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("end", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_box(1);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_19, x_20);
lean_dec(x_19);
x_22 = 0;
x_23 = l_Lean_mkIdentFrom(x_21, x_16, x_22);
x_24 = lean_ctor_get(x_2, 5);
x_25 = l_Lean_replaceRef(x_21, x_24);
lean_dec(x_21);
x_26 = l_Lean_SourceInfo_fromRef(x_25, x_22);
lean_dec(x_25);
x_27 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3;
lean_inc(x_26);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_26);
x_28 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4;
lean_inc(x_23);
lean_inc(x_26);
x_29 = l_Lean_Syntax_node2(x_26, x_28, x_12, x_23);
x_30 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
lean_inc(x_26);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
lean_inc(x_26);
x_33 = l_Lean_Syntax_node1(x_26, x_32, x_23);
x_34 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6;
lean_inc(x_26);
x_35 = l_Lean_Syntax_node2(x_26, x_34, x_31, x_33);
x_36 = l_Lean_Syntax_node3(x_26, x_32, x_29, x_17, x_35);
lean_ctor_set(x_4, 0, x_36);
return x_4;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_40, x_41);
lean_dec(x_40);
x_43 = 0;
x_44 = l_Lean_mkIdentFrom(x_42, x_37, x_43);
x_45 = lean_ctor_get(x_2, 5);
x_46 = l_Lean_replaceRef(x_42, x_45);
lean_dec(x_42);
x_47 = l_Lean_SourceInfo_fromRef(x_46, x_43);
lean_dec(x_46);
x_48 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3;
lean_inc(x_47);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4;
lean_inc(x_44);
lean_inc(x_47);
x_51 = l_Lean_Syntax_node2(x_47, x_50, x_49, x_44);
x_52 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
lean_inc(x_47);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
lean_inc(x_47);
x_55 = l_Lean_Syntax_node1(x_47, x_54, x_44);
x_56 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6;
lean_inc(x_47);
x_57 = l_Lean_Syntax_node2(x_47, x_56, x_53, x_55);
x_58 = l_Lean_Syntax_node3(x_47, x_54, x_51, x_38, x_57);
lean_ctor_set(x_4, 0, x_58);
return x_4;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
lean_dec(x_4);
x_60 = lean_ctor_get(x_12, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_12, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_62 = x_12;
} else {
 lean_dec_ref(x_12);
 x_62 = lean_box(0);
}
x_63 = lean_unsigned_to_nat(1u);
x_64 = l_Lean_Syntax_getArg(x_1, x_63);
lean_dec(x_1);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Syntax_getArg(x_64, x_65);
lean_dec(x_64);
x_67 = 0;
x_68 = l_Lean_mkIdentFrom(x_66, x_60, x_67);
x_69 = lean_ctor_get(x_2, 5);
x_70 = l_Lean_replaceRef(x_66, x_69);
lean_dec(x_66);
x_71 = l_Lean_SourceInfo_fromRef(x_70, x_67);
lean_dec(x_70);
x_72 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3;
lean_inc(x_71);
if (lean_is_scalar(x_62)) {
 x_73 = lean_alloc_ctor(2, 2, 0);
} else {
 x_73 = x_62;
 lean_ctor_set_tag(x_73, 2);
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4;
lean_inc(x_68);
lean_inc(x_71);
x_75 = l_Lean_Syntax_node2(x_71, x_74, x_73, x_68);
x_76 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
lean_inc(x_71);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
lean_inc(x_71);
x_79 = l_Lean_Syntax_node1(x_71, x_78, x_68);
x_80 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6;
lean_inc(x_71);
x_81 = l_Lean_Syntax_node2(x_71, x_80, x_77, x_79);
x_82 = l_Lean_Syntax_node3(x_71, x_78, x_75, x_61, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_59);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_4);
if (x_84 == 0)
{
return x_4;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_4, 0);
x_86 = lean_ctor_get(x_4, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_4);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNamespacedDeclaration___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandNamespacedDeclaration(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandNamespacedDeclaration", 27, 27);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandNamespacedDeclaration___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Macro that expands a declaration with a complex name into an explicit `namespace` block.\nImplementing this step as a macro means that reuse checking is handled by `elabCommand`.\n ", 179, 179);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1___closed__1;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(196u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(203u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(34u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(196u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(196u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_elabStructure(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_elabClassInductive(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_elabInductive(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_elabAxiom(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected declaration", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_inc(x_6);
x_7 = l_Lean_Syntax_getKind(x_6);
lean_inc(x_6);
x_8 = l_Lean_Elab_Command_isDefLike(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__15;
x_10 = lean_name_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__17;
x_12 = lean_name_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__19;
x_14 = lean_name_eq(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__21;
x_16 = lean_name_eq(x_7, x_15);
lean_dec(x_7);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_1);
x_17 = 1;
x_18 = l_Lean_Elab_Command_elabDeclaration___closed__3;
x_19 = l_Lean_Elab_Command_withoutCommandIncrementality___rarg(x_17, x_18, x_2, x_3, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___lambda__1___boxed), 5, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_6);
x_23 = 1;
x_24 = l_Lean_Elab_Command_withoutCommandIncrementality___rarg(x_23, x_22, x_2, x_3, x_4);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_7);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
lean_dec(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___lambda__2___boxed), 5, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_6);
x_28 = 1;
x_29 = l_Lean_Elab_Command_withoutCommandIncrementality___rarg(x_28, x_27, x_2, x_3, x_4);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_7);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Syntax_getArg(x_1, x_30);
lean_dec(x_1);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___lambda__3___boxed), 5, 2);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_6);
x_33 = 1;
x_34 = l_Lean_Elab_Command_withoutCommandIncrementality___rarg(x_33, x_32, x_2, x_3, x_4);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_dec(x_7);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
lean_dec(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___lambda__4___boxed), 5, 2);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_6);
x_38 = 1;
x_39 = l_Lean_Elab_Command_withoutCommandIncrementality___rarg(x_38, x_37, x_2, x_3, x_4);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_mk(x_41);
x_43 = l_Lean_Elab_Command_elabMutualDef(x_42, x_2, x_3, x_4);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabDeclaration___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabDeclaration___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabDeclaration___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclaration___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabDeclaration___lambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabDeclaration", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(206u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(226u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(41u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(206u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(206u);
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(19u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__2;
x_3 = l_Lean_Elab_addBuiltinIncrementalElab(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__17;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
goto _start;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1(x_4, x_9, x_10);
lean_dec(x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = l_Lean_Syntax_getArg(x_9, x_10);
lean_inc(x_4);
x_13 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_12, x_4, x_5, x_6);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_9, x_16);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView(x_14, x_17, x_4, x_5, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_11, x_2, x_19);
x_2 = x_22;
x_3 = x_23;
x_6 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_array_size(x_1);
x_6 = 0;
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1(x_5, x_6, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_elabInductiveViews(x_8, x_2, x_3, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive___spec__1(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_isDefLike(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1(x_4, x_9, x_10);
lean_dec(x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("variable", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("universe", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("set_option", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("open", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6;
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8;
x_10 = lean_name_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10;
x_12 = lean_name_eq(x_2, x_11);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = 1;
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Array_toSubarray___rarg(x_1, x_8, x_2);
x_11 = l_Array_ofSubarray___rarg(x_10);
lean_dec(x_10);
x_12 = l_Array_toSubarray___rarg(x_1, x_2, x_3);
x_13 = l_Array_ofSubarray___rarg(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_findCommon(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_name_eq(x_5, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Command_findCommonPrefix_findCommon(x_6, x_8);
x_12 = l_Lean_Name_append(x_5, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_findCommon___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_findCommonPrefix_findCommon(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Name_components(x_1);
x_7 = l_Lean_Name_components(x_4);
x_8 = l_Lean_Elab_Command_findCommonPrefix_findCommon(x_6, x_7);
lean_dec(x_7);
x_1 = x_8;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_findCommonPrefix(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Elab_Command_findCommonPrefix_go(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_1, x_3);
x_10 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_expandDeclNamespace_x3f(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(1);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_push(x_4, x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_4 = x_21;
x_6 = x_19;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_instMonad(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__1;
x_2 = l_Lean_instInhabitedSyntax;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__3;
x_5 = lean_panic_fn(x_4, x_1);
x_6 = lean_apply_2(x_5, x_2, x_3);
return x_6;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Command.expandMutualNamespace", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__5;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__1;
x_3 = lean_unsigned_to_nat(308u);
x_4 = lean_unsigned_to_nat(40u);
x_5 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_4, x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_4, x_3, x_10);
lean_inc(x_9);
x_12 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_getDefName_x3f(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__3;
lean_inc(x_5);
x_14 = l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2(x_13, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_11, x_3, x_15);
x_3 = x_18;
x_4 = x_19;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = l_Lean_extractMacroScopes(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_box(0);
x_30 = l_Lean_Name_replacePrefix(x_28, x_1, x_29);
lean_ctor_set(x_26, 0, x_30);
x_31 = l_Lean_MacroScopesView_review(x_26);
x_32 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(x_9, x_31);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_35 = lean_array_uset(x_11, x_3, x_32);
x_3 = x_34;
x_4 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
x_39 = lean_ctor_get(x_26, 2);
x_40 = lean_ctor_get(x_26, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_41 = lean_box(0);
x_42 = l_Lean_Name_replacePrefix(x_37, x_1, x_41);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_39);
lean_ctor_set(x_43, 3, x_40);
x_44 = l_Lean_MacroScopesView_review(x_43);
x_45 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName(x_9, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_48 = lean_array_uset(x_11, x_3, x_45);
x_3 = x_47;
x_4 = x_48;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_array_size(x_1);
lean_inc(x_6);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3(x_2, x_8, x_3, x_1, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = 0;
x_13 = l_Lean_mkIdentFrom(x_4, x_2, x_12);
x_14 = lean_box(2);
x_15 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_11);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_setArg(x_4, x_17, x_16);
x_19 = lean_ctor_get(x_6, 5);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l_Lean_SourceInfo_fromRef(x_19, x_12);
lean_dec(x_19);
x_21 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3;
lean_inc(x_20);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4;
lean_inc(x_13);
lean_inc(x_20);
x_24 = l_Lean_Syntax_node2(x_20, x_23, x_22, x_13);
x_25 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
lean_inc(x_20);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_20);
x_27 = l_Lean_Syntax_node1(x_20, x_15, x_13);
x_28 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6;
lean_inc(x_20);
x_29 = l_Lean_Syntax_node2(x_20, x_28, x_26, x_27);
x_30 = l_Lean_Syntax_node3(x_20, x_15, x_24, x_18, x_29);
lean_ctor_set(x_9, 0, x_30);
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = 0;
x_34 = l_Lean_mkIdentFrom(x_4, x_2, x_33);
x_35 = lean_box(2);
x_36 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_31);
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_Lean_Syntax_setArg(x_4, x_38, x_37);
x_40 = lean_ctor_get(x_6, 5);
lean_inc(x_40);
lean_dec(x_6);
x_41 = l_Lean_SourceInfo_fromRef(x_40, x_33);
lean_dec(x_40);
x_42 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3;
lean_inc(x_41);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4;
lean_inc(x_34);
lean_inc(x_41);
x_45 = l_Lean_Syntax_node2(x_41, x_44, x_43, x_34);
x_46 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
lean_inc(x_41);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_41);
x_48 = l_Lean_Syntax_node1(x_41, x_36, x_34);
x_49 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6;
lean_inc(x_41);
x_50 = l_Lean_Syntax_node2(x_41, x_49, x_47, x_48);
x_51 = l_Lean_Syntax_node3(x_41, x_36, x_45, x_39, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_32);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
return x_9;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_9, 0);
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_9);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4;
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1(x_6, x_7, x_8, x_9, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_array_to_list(x_12);
x_15 = l_Lean_Elab_Command_findCommonPrefix(x_14);
x_16 = l_Lean_Name_isAnonymous(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Command_expandMutualNamespace___lambda__1(x_6, x_15, x_8, x_1, x_17, x_2, x_13);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(1);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_array_to_list(x_20);
x_23 = l_Lean_Elab_Command_findCommonPrefix(x_22);
x_24 = l_Lean_Name_isAnonymous(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Command_expandMutualNamespace___lambda__1(x_6, x_23, x_8, x_1, x_25, x_2, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualNamespace___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualNamespace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Lean_Elab_Command_expandMutualNamespace___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mutual", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandMutualNamespace", 21, 21);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualNamespace), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(295u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(310u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(38u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(295u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(295u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(25u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Macro_expandMacro_x3f(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_array_push(x_2, x_1);
x_12 = lean_box(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_array_push(x_2, x_1);
x_17 = lean_box(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_array_push(x_2, x_24);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_8, 0, x_28);
return x_7;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_array_push(x_2, x_29);
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_ctor_get(x_8, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_37 = x_8;
} else {
 lean_dec_ref(x_8);
 x_37 = lean_box(0);
}
x_38 = lean_array_push(x_2, x_36);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
if (lean_is_scalar(x_37)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_37;
}
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
return x_7;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_1, x_3);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_9);
x_14 = l_Lean_Syntax_isOfKind(x_9, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_free_object(x_4);
x_15 = lean_box(0);
x_16 = lean_unbox(x_12);
lean_dec(x_12);
lean_inc(x_5);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___lambda__1(x_9, x_11, x_16, x_15, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
x_4 = x_26;
x_6 = x_25;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
size_t x_34; size_t x_35; 
lean_dec(x_9);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
x_39 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_9);
x_40 = l_Lean_Syntax_isOfKind(x_9, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_box(0);
x_42 = lean_unbox(x_38);
lean_dec(x_38);
lean_inc(x_5);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___lambda__1(x_9, x_37, x_42, x_41, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_5);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = 1;
x_52 = lean_usize_add(x_3, x_51);
x_3 = x_52;
x_4 = x_50;
x_6 = x_49;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; 
lean_dec(x_9);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_38);
x_59 = 1;
x_60 = lean_usize_add(x_3, x_59);
x_3 = x_60;
x_4 = x_58;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualElement___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualElement(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l_Lean_Elab_Command_expandMutualElement___closed__1;
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1(x_6, x_7, x_8, x_9, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(1);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_box(2);
x_24 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
x_26 = l_Lean_Syntax_setArg(x_1, x_4, x_25);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_box(2);
x_30 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
x_32 = l_Lean_Syntax_setArg(x_1, x_4, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandMutualElement___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandMutualElement", 19, 19);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualElement), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(313u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(327u);
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(26u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(313u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(313u);
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(23u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualPreamble___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("section", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualPreamble___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_expandMutualPreamble___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMutualPreamble___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_splitMutualPreamble_loop(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_2, 5);
x_16 = 0;
x_17 = l_Lean_SourceInfo_fromRef(x_15, x_16);
x_18 = l_Lean_Elab_Command_expandMutualPreamble___closed__1;
lean_inc(x_17);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_17);
x_19 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_20 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_17);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_Elab_Command_expandMutualPreamble___closed__2;
lean_inc(x_21);
lean_inc(x_17);
x_23 = l_Lean_Syntax_node2(x_17, x_22, x_11, x_21);
x_24 = lean_box(2);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_14);
x_26 = l_Lean_Syntax_setArg(x_1, x_4, x_25);
x_27 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
lean_inc(x_17);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6;
x_30 = l_Lean_Syntax_node2(x_17, x_29, x_28, x_21);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_mk(x_32);
x_34 = l_Array_append___rarg(x_33, x_13);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_array_mk(x_35);
x_37 = l_Array_append___rarg(x_34, x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_31);
x_39 = lean_array_mk(x_38);
x_40 = l_Array_append___rarg(x_37, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_19);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_ctor_get(x_2, 5);
x_46 = 0;
x_47 = l_Lean_SourceInfo_fromRef(x_45, x_46);
x_48 = l_Lean_Elab_Command_expandMutualPreamble___closed__1;
lean_inc(x_47);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_51 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_47);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Lean_Elab_Command_expandMutualPreamble___closed__2;
lean_inc(x_52);
lean_inc(x_47);
x_54 = l_Lean_Syntax_node2(x_47, x_53, x_49, x_52);
x_55 = lean_box(2);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_44);
x_57 = l_Lean_Syntax_setArg(x_1, x_4, x_56);
x_58 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5;
lean_inc(x_47);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6;
x_61 = l_Lean_Syntax_node2(x_47, x_60, x_59, x_52);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_mk(x_63);
x_65 = l_Array_append___rarg(x_64, x_43);
lean_dec(x_43);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_62);
x_67 = lean_array_mk(x_66);
x_68 = l_Array_append___rarg(x_65, x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_62);
x_70 = lean_array_mk(x_69);
x_71 = l_Array_append___rarg(x_68, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_55);
lean_ctor_set(x_72, 1, x_50);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_3);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMutualPreamble___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandMutualPreamble(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandMutualPreamble", 20, 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMutualPreamble___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(330u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(337u);
x_2 = lean_unsigned_to_nat(74u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(74u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(330u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(330u);
x_2 = lean_unsigned_to_nat(24u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(24u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid mutual block: either all elements of the block must be inductive declarations, or they must all be definitions/theorems/abbrevs", 135, 135);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualDef(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualInductive(x_1);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
x_8 = l_Lean_Elab_Command_elabMutual___closed__3;
x_9 = l_Lean_Elab_Command_withoutCommandIncrementality___rarg(x_7, x_8, x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_elabMutualInductive), 4, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = 1;
x_15 = l_Lean_Elab_Command_withoutCommandIncrementality___rarg(x_14, x_13, x_2, x_3, x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = l_Lean_Elab_Command_elabMutualDef(x_18, x_2, x_3, x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMutual___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabMutual(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabMutual", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMutual___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(340u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(348u);
x_2 = lean_unsigned_to_nat(154u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(154u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(340u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(340u);
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(14u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__2;
x_3 = l_Lean_Elab_addBuiltinIncrementalElab(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eraseAttr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown attribute [", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_14 = l_Lean_Syntax_getKind(x_10);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2;
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_array_push(x_12, x_10);
lean_ctor_set(x_4, 0, x_17);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_10, x_21);
x_23 = l_Lean_Syntax_getId(x_22);
lean_dec(x_22);
x_24 = lean_erase_macro_scopes(x_23);
x_25 = lean_st_ref_get(x_6, x_7);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_isAttribute(x_29, x_24);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_31 = l_Lean_MessageData_ofName(x_24);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_31);
lean_ctor_set(x_25, 0, x_32);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__6;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
x_35 = 2;
lean_inc(x_5);
x_36 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_10, x_34, x_35, x_5, x_6, x_28);
lean_dec(x_10);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_3 = x_39;
x_7 = x_37;
goto _start;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; 
lean_free_object(x_25);
lean_dec(x_10);
x_41 = lean_array_push(x_13, x_24);
lean_ctor_set(x_4, 1, x_41);
x_42 = 1;
x_43 = lean_usize_add(x_3, x_42);
x_3 = x_43;
x_7 = x_28;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_isAttribute(x_47, x_24);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_49 = l_Lean_MessageData_ofName(x_24);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__6;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = 2;
lean_inc(x_5);
x_55 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_10, x_53, x_54, x_5, x_6, x_46);
lean_dec(x_10);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = 1;
x_58 = lean_usize_add(x_3, x_57);
x_3 = x_58;
x_7 = x_56;
goto _start;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; 
lean_dec(x_10);
x_60 = lean_array_push(x_13, x_24);
lean_ctor_set(x_4, 1, x_60);
x_61 = 1;
x_62 = lean_usize_add(x_3, x_61);
x_3 = x_62;
x_7 = x_46;
goto _start;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_10);
x_66 = l_Lean_Syntax_getKind(x_10);
x_67 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2;
x_68 = lean_name_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; 
x_69 = lean_array_push(x_64, x_10);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
x_71 = 1;
x_72 = lean_usize_add(x_3, x_71);
x_3 = x_72;
x_4 = x_70;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg(x_10, x_74);
x_76 = l_Lean_Syntax_getId(x_75);
lean_dec(x_75);
x_77 = lean_erase_macro_scopes(x_76);
x_78 = lean_st_ref_get(x_6, x_7);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l_Lean_isAttribute(x_82, x_77);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; 
x_84 = l_Lean_MessageData_ofName(x_77);
x_85 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4;
if (lean_is_scalar(x_81)) {
 x_86 = lean_alloc_ctor(7, 2, 0);
} else {
 x_86 = x_81;
 lean_ctor_set_tag(x_86, 7);
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__6;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = 2;
lean_inc(x_5);
x_90 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_10, x_88, x_89, x_5, x_6, x_80);
lean_dec(x_10);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_64);
lean_ctor_set(x_92, 1, x_65);
x_93 = 1;
x_94 = lean_usize_add(x_3, x_93);
x_3 = x_94;
x_4 = x_92;
x_7 = x_91;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; 
lean_dec(x_81);
lean_dec(x_10);
x_96 = lean_array_push(x_65, x_77);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_64);
lean_ctor_set(x_97, 1, x_96);
x_98 = 1;
x_99 = lean_usize_add(x_3, x_98);
x_3 = x_99;
x_4 = x_97;
x_7 = x_80;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Command_elabAttr___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_instMonadTermElabM;
x_2 = l_Lean_instInhabitedName;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Command_elabAttr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Elab_Command_elabAttr___spec__3___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ResolveName", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ensureNonAmbiguous", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__1;
x_2 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(364u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ambiguous identifier '", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', possible interpretations: ", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__3;
x_11 = l_panic___at_Lean_Elab_Command_elabAttr___spec__3(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_20 = l_Lean_Syntax_formatStxAux(x_17, x_18, x_19, x_1);
x_21 = l_Std_Format_defWidth;
x_22 = lean_format_pretty(x_20, x_21, x_19, x_19);
x_23 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__4;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__5;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_List_mapTR_loop___at_Lean_ensureNonAmbiguous___spec__2(x_2, x_27);
x_29 = l_List_toString___at_Lean_ensureNoOverload___spec__2(x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_26, x_29);
lean_dec(x_29);
x_31 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__8;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
x_35 = l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_16 = l_Lean_Attribute_erase(x_1, x_15, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_20 = lean_box(0);
x_4 = x_19;
x_5 = x_20;
x_12 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_1, x_9);
x_11 = l_Lean_MessageData_ofExpr(x_10);
x_12 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__4;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_16 = l_Lean_Elab_Term_applyAttributes(x_14, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_size(x_3);
x_19 = lean_box(0);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4(x_14, x_3, x_18, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_12 = l_Lean_Elab_realizeGlobalConstWithInfos(x_1, x_2, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_8(x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
x_19 = l_Lean_Exception_isInterrupt(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isRuntime(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_free_object(x_12);
lean_dec(x_17);
x_21 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_22 = lean_erase_macro_scopes(x_21);
x_23 = l_Lean_Meta_Simp_isBuiltinSimproc(x_22, x_9, x_10, x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 1);
x_34 = lean_ctor_get(x_23, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 0, x_22);
x_35 = lean_apply_8(x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_4);
x_38 = lean_apply_8(x_3, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
return x_38;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = l_Lean_Exception_isInterrupt(x_39);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Exception_isRuntime(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_39);
x_43 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_44 = lean_erase_macro_scopes(x_43);
x_45 = l_Lean_Meta_Simp_isBuiltinSimproc(x_44, x_9, x_10, x_40);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5(x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_55 = x_45;
} else {
 lean_dec_ref(x_45);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_4);
x_57 = lean_apply_8(x_3, x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_39);
lean_ctor_set(x_58, 1, x_40);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_40);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_14 = lean_array_uget(x_5, x_7);
x_15 = lean_box_usize(x_2);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__1___boxed), 12, 4);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_15);
x_17 = lean_box(0);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__2), 11, 4);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_1);
x_19 = l_Lean_Elab_Command_getRef(x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_replaceRef(x_14, x_20);
lean_dec(x_20);
lean_dec(x_14);
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 2);
x_26 = lean_ctor_get(x_9, 3);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_ctor_get(x_9, 5);
x_29 = lean_ctor_get(x_9, 7);
x_30 = lean_ctor_get(x_9, 8);
x_31 = lean_ctor_get(x_9, 9);
x_32 = lean_ctor_get_uint8(x_9, sizeof(void*)*10);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_33 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_28);
lean_ctor_set(x_33, 6, x_22);
lean_ctor_set(x_33, 7, x_29);
lean_ctor_set(x_33, 8, x_30);
lean_ctor_set(x_33, 9, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*10, x_32);
x_34 = l_Lean_Elab_Command_liftTermElabM___rarg(x_18, x_33, x_10, x_21);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = 1;
x_37 = lean_usize_add(x_7, x_36);
x_38 = lean_box(0);
x_7 = x_37;
x_8 = x_38;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAttr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getSepArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_size(x_8);
x_10 = 0;
x_11 = l_Lean_Elab_Command_elabAttr___closed__1;
lean_inc(x_2);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1(x_8, x_9, x_10, x_11, x_2, x_3, x_4);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_2);
x_17 = l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3(x_15, x_2, x_3, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(4u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l_Lean_Syntax_getArgs(x_21);
lean_dec(x_21);
x_23 = lean_array_size(x_22);
x_24 = lean_box(0);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6(x_5, x_10, x_16, x_18, x_22, x_23, x_10, x_24, x_2, x_3, x_19);
lean_dec(x_2);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_16);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___lambda__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__6(x_1, x_12, x_3, x_4, x_5, x_13, x_14, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabAttr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attribute", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabAttr", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAttr___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(351u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(383u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(39u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(351u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(351u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(40u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(48u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid initialization command, unexpected modifiers", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attributes", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attrInstance", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attrKind", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Attr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simple", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__11;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declId", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__17;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optDeclSig", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__20;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeSpec", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__22;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__25;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__27;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__27;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__31;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__30;
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__32;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__34;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__34;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__38;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__37;
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__39;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declValSimple", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__41;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("do", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Termination", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("suffix", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__45;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__46;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_matchesNull(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_15 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_14, x_7, x_8, x_9);
lean_dec(x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_matchesNull(x_17, x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_20 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_19, x_7, x_8, x_9);
lean_dec(x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Syntax_matchesNull(x_22, x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_25 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_24, x_7, x_8, x_9);
lean_dec(x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
x_28 = l_Lean_Syntax_matchesNull(x_27, x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_30 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_29, x_7, x_8, x_9);
lean_dec(x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_unsigned_to_nat(5u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = l_Lean_Syntax_matchesNull(x_32, x_12);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_35 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_34, x_7, x_8, x_9);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Elab_Command_getRef(x_7, x_8, x_9);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = 0;
x_41 = l_Lean_SourceInfo_fromRef(x_38, x_40);
lean_dec(x_38);
x_42 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_39);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_45);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
lean_inc(x_41);
lean_ctor_set_tag(x_46, 2);
lean_ctor_set(x_46, 1, x_50);
lean_ctor_set(x_46, 0, x_41);
x_51 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_52 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_41);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_inc(x_53);
lean_inc(x_41);
x_55 = l_Lean_Syntax_node1(x_41, x_54, x_53);
x_56 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_inc(x_53);
lean_inc(x_41);
x_57 = l_Lean_Syntax_node2(x_41, x_56, x_2, x_53);
x_58 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
lean_inc(x_41);
x_59 = l_Lean_Syntax_node2(x_41, x_58, x_55, x_57);
lean_inc(x_41);
x_60 = l_Lean_Syntax_node1(x_41, x_51, x_59);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_inc(x_41);
lean_ctor_set_tag(x_42, 2);
lean_ctor_set(x_42, 1, x_61);
lean_ctor_set(x_42, 0, x_41);
x_62 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_41);
x_63 = l_Lean_Syntax_node3(x_41, x_62, x_46, x_60, x_42);
lean_inc(x_41);
x_64 = l_Lean_Syntax_node1(x_41, x_51, x_63);
x_65 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_41);
lean_ctor_set_tag(x_36, 2);
lean_ctor_set(x_36, 1, x_65);
lean_ctor_set(x_36, 0, x_41);
x_66 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_44);
lean_inc(x_48);
x_67 = l_Lean_addMacroScope(x_48, x_66, x_44);
x_68 = lean_box(0);
x_69 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_41);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_41);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_68);
x_71 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_53);
lean_inc(x_41);
x_72 = l_Lean_Syntax_node2(x_41, x_71, x_70, x_53);
x_73 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_41);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_41);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
lean_inc(x_44);
lean_inc(x_48);
x_76 = l_Lean_addMacroScope(x_48, x_75, x_44);
x_77 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_78 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_41);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_78);
x_80 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36;
x_81 = l_Lean_addMacroScope(x_48, x_80, x_44);
x_82 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35;
x_83 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40;
lean_inc(x_41);
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_41);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_84, 3, x_83);
lean_inc(x_41);
x_85 = l_Lean_Syntax_node1(x_41, x_51, x_84);
x_86 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_41);
x_87 = l_Lean_Syntax_node2(x_41, x_86, x_79, x_85);
x_88 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_41);
x_89 = l_Lean_Syntax_node2(x_41, x_88, x_74, x_87);
lean_inc(x_41);
x_90 = l_Lean_Syntax_node1(x_41, x_51, x_89);
x_91 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_53);
lean_inc(x_41);
x_92 = l_Lean_Syntax_node2(x_41, x_91, x_53, x_90);
x_93 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_41);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_41);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_41);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_41);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_41);
x_98 = l_Lean_Syntax_node2(x_41, x_97, x_96, x_3);
x_99 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_53, 2);
lean_inc(x_41);
x_100 = l_Lean_Syntax_node2(x_41, x_99, x_53, x_53);
x_101 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_53);
lean_inc(x_41);
x_102 = l_Lean_Syntax_node4(x_41, x_101, x_94, x_98, x_100, x_53);
x_103 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_53);
lean_inc(x_41);
x_104 = l_Lean_Syntax_node5(x_41, x_103, x_36, x_72, x_92, x_102, x_53);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_41);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_41);
lean_ctor_set(x_106, 1, x_51);
lean_ctor_set(x_106, 2, x_105);
lean_inc_n(x_53, 3);
lean_inc(x_41);
x_107 = l_Lean_Syntax_node6(x_41, x_4, x_106, x_64, x_53, x_53, x_53, x_53);
x_108 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_109 = l_Lean_Syntax_node2(x_41, x_108, x_107, x_104);
x_110 = l_Lean_Elab_Command_elabCommand(x_109, x_7, x_8, x_49);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_111 = lean_ctor_get(x_6, 0);
lean_inc(x_111);
lean_dec(x_6);
x_112 = l_Array_mkArray1___rarg(x_111);
x_113 = l_Array_append___rarg(x_52, x_112);
lean_dec(x_112);
lean_inc(x_41);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_41);
lean_ctor_set(x_114, 1, x_51);
lean_ctor_set(x_114, 2, x_113);
lean_inc_n(x_53, 3);
lean_inc(x_41);
x_115 = l_Lean_Syntax_node6(x_41, x_4, x_114, x_64, x_53, x_53, x_53, x_53);
x_116 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_117 = l_Lean_Syntax_node2(x_41, x_116, x_115, x_104);
x_118 = l_Lean_Elab_Command_elabCommand(x_117, x_7, x_8, x_49);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_119 = lean_ctor_get(x_46, 0);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_46);
x_121 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
lean_inc(x_41);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_41);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_124 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_41);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_41);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_124);
x_126 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_inc(x_125);
lean_inc(x_41);
x_127 = l_Lean_Syntax_node1(x_41, x_126, x_125);
x_128 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_inc(x_125);
lean_inc(x_41);
x_129 = l_Lean_Syntax_node2(x_41, x_128, x_2, x_125);
x_130 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
lean_inc(x_41);
x_131 = l_Lean_Syntax_node2(x_41, x_130, x_127, x_129);
lean_inc(x_41);
x_132 = l_Lean_Syntax_node1(x_41, x_123, x_131);
x_133 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_inc(x_41);
lean_ctor_set_tag(x_42, 2);
lean_ctor_set(x_42, 1, x_133);
lean_ctor_set(x_42, 0, x_41);
x_134 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_41);
x_135 = l_Lean_Syntax_node3(x_41, x_134, x_122, x_132, x_42);
lean_inc(x_41);
x_136 = l_Lean_Syntax_node1(x_41, x_123, x_135);
x_137 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_41);
lean_ctor_set_tag(x_36, 2);
lean_ctor_set(x_36, 1, x_137);
lean_ctor_set(x_36, 0, x_41);
x_138 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_44);
lean_inc(x_119);
x_139 = l_Lean_addMacroScope(x_119, x_138, x_44);
x_140 = lean_box(0);
x_141 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_41);
x_142 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_142, 0, x_41);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_140);
x_143 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_125);
lean_inc(x_41);
x_144 = l_Lean_Syntax_node2(x_41, x_143, x_142, x_125);
x_145 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_41);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_41);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
lean_inc(x_44);
lean_inc(x_119);
x_148 = l_Lean_addMacroScope(x_119, x_147, x_44);
x_149 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_150 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_41);
x_151 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_151, 0, x_41);
lean_ctor_set(x_151, 1, x_149);
lean_ctor_set(x_151, 2, x_148);
lean_ctor_set(x_151, 3, x_150);
x_152 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36;
x_153 = l_Lean_addMacroScope(x_119, x_152, x_44);
x_154 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35;
x_155 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40;
lean_inc(x_41);
x_156 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_156, 0, x_41);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_153);
lean_ctor_set(x_156, 3, x_155);
lean_inc(x_41);
x_157 = l_Lean_Syntax_node1(x_41, x_123, x_156);
x_158 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_41);
x_159 = l_Lean_Syntax_node2(x_41, x_158, x_151, x_157);
x_160 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_41);
x_161 = l_Lean_Syntax_node2(x_41, x_160, x_146, x_159);
lean_inc(x_41);
x_162 = l_Lean_Syntax_node1(x_41, x_123, x_161);
x_163 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_125);
lean_inc(x_41);
x_164 = l_Lean_Syntax_node2(x_41, x_163, x_125, x_162);
x_165 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_41);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_41);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_41);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_41);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_41);
x_170 = l_Lean_Syntax_node2(x_41, x_169, x_168, x_3);
x_171 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_125, 2);
lean_inc(x_41);
x_172 = l_Lean_Syntax_node2(x_41, x_171, x_125, x_125);
x_173 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_125);
lean_inc(x_41);
x_174 = l_Lean_Syntax_node4(x_41, x_173, x_166, x_170, x_172, x_125);
x_175 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_125);
lean_inc(x_41);
x_176 = l_Lean_Syntax_node5(x_41, x_175, x_36, x_144, x_164, x_174, x_125);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_41);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_41);
lean_ctor_set(x_178, 1, x_123);
lean_ctor_set(x_178, 2, x_177);
lean_inc_n(x_125, 3);
lean_inc(x_41);
x_179 = l_Lean_Syntax_node6(x_41, x_4, x_178, x_136, x_125, x_125, x_125, x_125);
x_180 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_181 = l_Lean_Syntax_node2(x_41, x_180, x_179, x_176);
x_182 = l_Lean_Elab_Command_elabCommand(x_181, x_7, x_8, x_120);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_183 = lean_ctor_get(x_6, 0);
lean_inc(x_183);
lean_dec(x_6);
x_184 = l_Array_mkArray1___rarg(x_183);
x_185 = l_Array_append___rarg(x_124, x_184);
lean_dec(x_184);
lean_inc(x_41);
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_41);
lean_ctor_set(x_186, 1, x_123);
lean_ctor_set(x_186, 2, x_185);
lean_inc_n(x_125, 3);
lean_inc(x_41);
x_187 = l_Lean_Syntax_node6(x_41, x_4, x_186, x_136, x_125, x_125, x_125, x_125);
x_188 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_189 = l_Lean_Syntax_node2(x_41, x_188, x_187, x_176);
x_190 = l_Lean_Elab_Command_elabCommand(x_189, x_7, x_8, x_120);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_191 = lean_ctor_get(x_42, 0);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_42);
x_193 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
x_197 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
lean_inc(x_41);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(2, 2, 0);
} else {
 x_198 = x_196;
 lean_ctor_set_tag(x_198, 2);
}
lean_ctor_set(x_198, 0, x_41);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_200 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_41);
x_201 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_201, 0, x_41);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
x_202 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_inc(x_201);
lean_inc(x_41);
x_203 = l_Lean_Syntax_node1(x_41, x_202, x_201);
x_204 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_inc(x_201);
lean_inc(x_41);
x_205 = l_Lean_Syntax_node2(x_41, x_204, x_2, x_201);
x_206 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
lean_inc(x_41);
x_207 = l_Lean_Syntax_node2(x_41, x_206, x_203, x_205);
lean_inc(x_41);
x_208 = l_Lean_Syntax_node1(x_41, x_199, x_207);
x_209 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_inc(x_41);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_41);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_41);
x_212 = l_Lean_Syntax_node3(x_41, x_211, x_198, x_208, x_210);
lean_inc(x_41);
x_213 = l_Lean_Syntax_node1(x_41, x_199, x_212);
x_214 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_41);
lean_ctor_set_tag(x_36, 2);
lean_ctor_set(x_36, 1, x_214);
lean_ctor_set(x_36, 0, x_41);
x_215 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_191);
lean_inc(x_194);
x_216 = l_Lean_addMacroScope(x_194, x_215, x_191);
x_217 = lean_box(0);
x_218 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_41);
x_219 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_219, 0, x_41);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_219, 2, x_216);
lean_ctor_set(x_219, 3, x_217);
x_220 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_201);
lean_inc(x_41);
x_221 = l_Lean_Syntax_node2(x_41, x_220, x_219, x_201);
x_222 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_41);
x_223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_223, 0, x_41);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
lean_inc(x_191);
lean_inc(x_194);
x_225 = l_Lean_addMacroScope(x_194, x_224, x_191);
x_226 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_227 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_41);
x_228 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_228, 0, x_41);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_227);
x_229 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36;
x_230 = l_Lean_addMacroScope(x_194, x_229, x_191);
x_231 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35;
x_232 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40;
lean_inc(x_41);
x_233 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_233, 0, x_41);
lean_ctor_set(x_233, 1, x_231);
lean_ctor_set(x_233, 2, x_230);
lean_ctor_set(x_233, 3, x_232);
lean_inc(x_41);
x_234 = l_Lean_Syntax_node1(x_41, x_199, x_233);
x_235 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_41);
x_236 = l_Lean_Syntax_node2(x_41, x_235, x_228, x_234);
x_237 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_41);
x_238 = l_Lean_Syntax_node2(x_41, x_237, x_223, x_236);
lean_inc(x_41);
x_239 = l_Lean_Syntax_node1(x_41, x_199, x_238);
x_240 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_201);
lean_inc(x_41);
x_241 = l_Lean_Syntax_node2(x_41, x_240, x_201, x_239);
x_242 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_41);
x_243 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_243, 0, x_41);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_41);
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_41);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_41);
x_247 = l_Lean_Syntax_node2(x_41, x_246, x_245, x_3);
x_248 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_201, 2);
lean_inc(x_41);
x_249 = l_Lean_Syntax_node2(x_41, x_248, x_201, x_201);
x_250 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_201);
lean_inc(x_41);
x_251 = l_Lean_Syntax_node4(x_41, x_250, x_243, x_247, x_249, x_201);
x_252 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_201);
lean_inc(x_41);
x_253 = l_Lean_Syntax_node5(x_41, x_252, x_36, x_221, x_241, x_251, x_201);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_254 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_41);
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_41);
lean_ctor_set(x_255, 1, x_199);
lean_ctor_set(x_255, 2, x_254);
lean_inc_n(x_201, 3);
lean_inc(x_41);
x_256 = l_Lean_Syntax_node6(x_41, x_4, x_255, x_213, x_201, x_201, x_201, x_201);
x_257 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_258 = l_Lean_Syntax_node2(x_41, x_257, x_256, x_253);
x_259 = l_Lean_Elab_Command_elabCommand(x_258, x_7, x_8, x_195);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_260 = lean_ctor_get(x_6, 0);
lean_inc(x_260);
lean_dec(x_6);
x_261 = l_Array_mkArray1___rarg(x_260);
x_262 = l_Array_append___rarg(x_200, x_261);
lean_dec(x_261);
lean_inc(x_41);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_41);
lean_ctor_set(x_263, 1, x_199);
lean_ctor_set(x_263, 2, x_262);
lean_inc_n(x_201, 3);
lean_inc(x_41);
x_264 = l_Lean_Syntax_node6(x_41, x_4, x_263, x_213, x_201, x_201, x_201, x_201);
x_265 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_266 = l_Lean_Syntax_node2(x_41, x_265, x_264, x_253);
x_267 = l_Lean_Elab_Command_elabCommand(x_266, x_7, x_8, x_195);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_268 = lean_ctor_get(x_36, 0);
x_269 = lean_ctor_get(x_36, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_36);
x_270 = 0;
x_271 = l_Lean_SourceInfo_fromRef(x_268, x_270);
lean_dec(x_268);
x_272 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_269);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_274);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
lean_inc(x_271);
if (lean_is_scalar(x_279)) {
 x_281 = lean_alloc_ctor(2, 2, 0);
} else {
 x_281 = x_279;
 lean_ctor_set_tag(x_281, 2);
}
lean_ctor_set(x_281, 0, x_271);
lean_ctor_set(x_281, 1, x_280);
x_282 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_283 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_271);
x_284 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_284, 0, x_271);
lean_ctor_set(x_284, 1, x_282);
lean_ctor_set(x_284, 2, x_283);
x_285 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_inc(x_284);
lean_inc(x_271);
x_286 = l_Lean_Syntax_node1(x_271, x_285, x_284);
x_287 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_inc(x_284);
lean_inc(x_271);
x_288 = l_Lean_Syntax_node2(x_271, x_287, x_2, x_284);
x_289 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
lean_inc(x_271);
x_290 = l_Lean_Syntax_node2(x_271, x_289, x_286, x_288);
lean_inc(x_271);
x_291 = l_Lean_Syntax_node1(x_271, x_282, x_290);
x_292 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_inc(x_271);
if (lean_is_scalar(x_275)) {
 x_293 = lean_alloc_ctor(2, 2, 0);
} else {
 x_293 = x_275;
 lean_ctor_set_tag(x_293, 2);
}
lean_ctor_set(x_293, 0, x_271);
lean_ctor_set(x_293, 1, x_292);
x_294 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_271);
x_295 = l_Lean_Syntax_node3(x_271, x_294, x_281, x_291, x_293);
lean_inc(x_271);
x_296 = l_Lean_Syntax_node1(x_271, x_282, x_295);
x_297 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_271);
x_298 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_298, 0, x_271);
lean_ctor_set(x_298, 1, x_297);
x_299 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_273);
lean_inc(x_277);
x_300 = l_Lean_addMacroScope(x_277, x_299, x_273);
x_301 = lean_box(0);
x_302 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_271);
x_303 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_303, 0, x_271);
lean_ctor_set(x_303, 1, x_302);
lean_ctor_set(x_303, 2, x_300);
lean_ctor_set(x_303, 3, x_301);
x_304 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_284);
lean_inc(x_271);
x_305 = l_Lean_Syntax_node2(x_271, x_304, x_303, x_284);
x_306 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_271);
x_307 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_307, 0, x_271);
lean_ctor_set(x_307, 1, x_306);
x_308 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
lean_inc(x_273);
lean_inc(x_277);
x_309 = l_Lean_addMacroScope(x_277, x_308, x_273);
x_310 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_311 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_271);
x_312 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_312, 0, x_271);
lean_ctor_set(x_312, 1, x_310);
lean_ctor_set(x_312, 2, x_309);
lean_ctor_set(x_312, 3, x_311);
x_313 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36;
x_314 = l_Lean_addMacroScope(x_277, x_313, x_273);
x_315 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35;
x_316 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40;
lean_inc(x_271);
x_317 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_317, 0, x_271);
lean_ctor_set(x_317, 1, x_315);
lean_ctor_set(x_317, 2, x_314);
lean_ctor_set(x_317, 3, x_316);
lean_inc(x_271);
x_318 = l_Lean_Syntax_node1(x_271, x_282, x_317);
x_319 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_271);
x_320 = l_Lean_Syntax_node2(x_271, x_319, x_312, x_318);
x_321 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_271);
x_322 = l_Lean_Syntax_node2(x_271, x_321, x_307, x_320);
lean_inc(x_271);
x_323 = l_Lean_Syntax_node1(x_271, x_282, x_322);
x_324 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_284);
lean_inc(x_271);
x_325 = l_Lean_Syntax_node2(x_271, x_324, x_284, x_323);
x_326 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_271);
x_327 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_327, 0, x_271);
lean_ctor_set(x_327, 1, x_326);
x_328 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_271);
x_329 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_329, 0, x_271);
lean_ctor_set(x_329, 1, x_328);
x_330 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_271);
x_331 = l_Lean_Syntax_node2(x_271, x_330, x_329, x_3);
x_332 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_284, 2);
lean_inc(x_271);
x_333 = l_Lean_Syntax_node2(x_271, x_332, x_284, x_284);
x_334 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_284);
lean_inc(x_271);
x_335 = l_Lean_Syntax_node4(x_271, x_334, x_327, x_331, x_333, x_284);
x_336 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_284);
lean_inc(x_271);
x_337 = l_Lean_Syntax_node5(x_271, x_336, x_298, x_305, x_325, x_335, x_284);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_338 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_271);
x_339 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_339, 0, x_271);
lean_ctor_set(x_339, 1, x_282);
lean_ctor_set(x_339, 2, x_338);
lean_inc_n(x_284, 3);
lean_inc(x_271);
x_340 = l_Lean_Syntax_node6(x_271, x_4, x_339, x_296, x_284, x_284, x_284, x_284);
x_341 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_342 = l_Lean_Syntax_node2(x_271, x_341, x_340, x_337);
x_343 = l_Lean_Elab_Command_elabCommand(x_342, x_7, x_8, x_278);
return x_343;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_344 = lean_ctor_get(x_6, 0);
lean_inc(x_344);
lean_dec(x_6);
x_345 = l_Array_mkArray1___rarg(x_344);
x_346 = l_Array_append___rarg(x_283, x_345);
lean_dec(x_345);
lean_inc(x_271);
x_347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_347, 0, x_271);
lean_ctor_set(x_347, 1, x_282);
lean_ctor_set(x_347, 2, x_346);
lean_inc_n(x_284, 3);
lean_inc(x_271);
x_348 = l_Lean_Syntax_node6(x_271, x_4, x_347, x_296, x_284, x_284, x_284, x_284);
x_349 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_350 = l_Lean_Syntax_node2(x_271, x_349, x_348, x_337);
x_351 = l_Lean_Elab_Command_elabCommand(x_350, x_7, x_8, x_278);
return x_351;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withDeclName", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("with_decl_name%", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsafe", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_6);
x_11 = l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1(x_6, x_1, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Lean_Elab_Command_getRef(x_8, x_9, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_17, x_19);
lean_dec(x_17);
x_21 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_9, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_30 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_20);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_20);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 1, x_32);
lean_ctor_set(x_25, 0, x_20);
x_33 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_23);
lean_inc(x_27);
x_34 = l_Lean_addMacroScope(x_27, x_33, x_23);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_20);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_35);
x_38 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_31);
lean_inc(x_20);
x_39 = l_Lean_Syntax_node2(x_20, x_38, x_37, x_31);
x_40 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_20);
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 1, x_40);
lean_ctor_set(x_21, 0, x_20);
x_41 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
x_42 = l_Lean_addMacroScope(x_27, x_41, x_23);
x_43 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_44 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_20);
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_44);
lean_inc(x_20);
x_46 = l_Lean_Syntax_node1(x_20, x_29, x_2);
x_47 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_20);
x_48 = l_Lean_Syntax_node2(x_20, x_47, x_45, x_46);
x_49 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_20);
x_50 = l_Lean_Syntax_node2(x_20, x_49, x_21, x_48);
lean_inc(x_20);
x_51 = l_Lean_Syntax_node1(x_20, x_29, x_50);
x_52 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_31);
lean_inc(x_20);
x_53 = l_Lean_Syntax_node2(x_20, x_52, x_31, x_51);
x_54 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_20);
lean_ctor_set_tag(x_15, 2);
lean_ctor_set(x_15, 1, x_54);
lean_ctor_set(x_15, 0, x_20);
x_55 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3;
lean_inc(x_20);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_55);
lean_ctor_set(x_11, 0, x_20);
x_56 = lean_mk_syntax_ident(x_6);
x_57 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_20);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_20);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_20);
x_60 = l_Lean_Syntax_node2(x_20, x_59, x_58, x_3);
x_61 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2;
lean_inc(x_31);
lean_inc(x_20);
x_62 = l_Lean_Syntax_node4(x_20, x_61, x_11, x_31, x_56, x_60);
x_63 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_31, 2);
lean_inc(x_20);
x_64 = l_Lean_Syntax_node2(x_20, x_63, x_31, x_31);
x_65 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_31);
lean_inc(x_20);
x_66 = l_Lean_Syntax_node4(x_20, x_65, x_15, x_62, x_64, x_31);
x_67 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_31);
lean_inc(x_20);
x_68 = l_Lean_Syntax_node5(x_20, x_67, x_25, x_39, x_53, x_66, x_31);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_20);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_20);
lean_ctor_set(x_70, 1, x_29);
lean_ctor_set(x_70, 2, x_69);
lean_inc_n(x_31, 4);
lean_inc(x_20);
x_71 = l_Lean_Syntax_node6(x_20, x_5, x_31, x_31, x_31, x_31, x_70, x_31);
x_72 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_20);
x_73 = l_Lean_Syntax_node2(x_20, x_72, x_71, x_68);
x_74 = l_Lean_Syntax_node2(x_20, x_29, x_73, x_1);
x_75 = l_Lean_Elab_Command_elabCommand(x_74, x_8, x_9, x_28);
return x_75;
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = lean_ctor_get(x_4, 0);
x_77 = 1;
x_78 = l_Lean_SourceInfo_fromRef(x_76, x_77);
x_79 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4;
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5;
lean_inc(x_20);
x_82 = l_Lean_Syntax_node1(x_20, x_81, x_80);
x_83 = l_Array_mkArray1___rarg(x_82);
x_84 = l_Array_append___rarg(x_30, x_83);
lean_dec(x_83);
lean_inc(x_20);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_20);
lean_ctor_set(x_85, 1, x_29);
lean_ctor_set(x_85, 2, x_84);
lean_inc_n(x_31, 4);
lean_inc(x_20);
x_86 = l_Lean_Syntax_node6(x_20, x_5, x_31, x_31, x_31, x_31, x_85, x_31);
x_87 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_20);
x_88 = l_Lean_Syntax_node2(x_20, x_87, x_86, x_68);
x_89 = l_Lean_Syntax_node2(x_20, x_29, x_88, x_1);
x_90 = l_Lean_Elab_Command_elabCommand(x_89, x_8, x_9, x_28);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_91 = lean_ctor_get(x_25, 0);
x_92 = lean_ctor_get(x_25, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_25);
x_93 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_94 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_20);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_20);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_20);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_20);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_23);
lean_inc(x_91);
x_99 = l_Lean_addMacroScope(x_91, x_98, x_23);
x_100 = lean_box(0);
x_101 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_20);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_20);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_100);
x_103 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_95);
lean_inc(x_20);
x_104 = l_Lean_Syntax_node2(x_20, x_103, x_102, x_95);
x_105 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_20);
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 1, x_105);
lean_ctor_set(x_21, 0, x_20);
x_106 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
x_107 = l_Lean_addMacroScope(x_91, x_106, x_23);
x_108 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_109 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_20);
x_110 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_110, 0, x_20);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_109);
lean_inc(x_20);
x_111 = l_Lean_Syntax_node1(x_20, x_93, x_2);
x_112 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_20);
x_113 = l_Lean_Syntax_node2(x_20, x_112, x_110, x_111);
x_114 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_20);
x_115 = l_Lean_Syntax_node2(x_20, x_114, x_21, x_113);
lean_inc(x_20);
x_116 = l_Lean_Syntax_node1(x_20, x_93, x_115);
x_117 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_95);
lean_inc(x_20);
x_118 = l_Lean_Syntax_node2(x_20, x_117, x_95, x_116);
x_119 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_20);
lean_ctor_set_tag(x_15, 2);
lean_ctor_set(x_15, 1, x_119);
lean_ctor_set(x_15, 0, x_20);
x_120 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3;
lean_inc(x_20);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_120);
lean_ctor_set(x_11, 0, x_20);
x_121 = lean_mk_syntax_ident(x_6);
x_122 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_20);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_20);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_20);
x_125 = l_Lean_Syntax_node2(x_20, x_124, x_123, x_3);
x_126 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2;
lean_inc(x_95);
lean_inc(x_20);
x_127 = l_Lean_Syntax_node4(x_20, x_126, x_11, x_95, x_121, x_125);
x_128 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_95, 2);
lean_inc(x_20);
x_129 = l_Lean_Syntax_node2(x_20, x_128, x_95, x_95);
x_130 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_95);
lean_inc(x_20);
x_131 = l_Lean_Syntax_node4(x_20, x_130, x_15, x_127, x_129, x_95);
x_132 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_95);
lean_inc(x_20);
x_133 = l_Lean_Syntax_node5(x_20, x_132, x_97, x_104, x_118, x_131, x_95);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_20);
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_20);
lean_ctor_set(x_135, 1, x_93);
lean_ctor_set(x_135, 2, x_134);
lean_inc_n(x_95, 4);
lean_inc(x_20);
x_136 = l_Lean_Syntax_node6(x_20, x_5, x_95, x_95, x_95, x_95, x_135, x_95);
x_137 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_20);
x_138 = l_Lean_Syntax_node2(x_20, x_137, x_136, x_133);
x_139 = l_Lean_Syntax_node2(x_20, x_93, x_138, x_1);
x_140 = l_Lean_Elab_Command_elabCommand(x_139, x_8, x_9, x_92);
return x_140;
}
else
{
lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_141 = lean_ctor_get(x_4, 0);
x_142 = 1;
x_143 = l_Lean_SourceInfo_fromRef(x_141, x_142);
x_144 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4;
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5;
lean_inc(x_20);
x_147 = l_Lean_Syntax_node1(x_20, x_146, x_145);
x_148 = l_Array_mkArray1___rarg(x_147);
x_149 = l_Array_append___rarg(x_94, x_148);
lean_dec(x_148);
lean_inc(x_20);
x_150 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_150, 0, x_20);
lean_ctor_set(x_150, 1, x_93);
lean_ctor_set(x_150, 2, x_149);
lean_inc_n(x_95, 4);
lean_inc(x_20);
x_151 = l_Lean_Syntax_node6(x_20, x_5, x_95, x_95, x_95, x_95, x_150, x_95);
x_152 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_20);
x_153 = l_Lean_Syntax_node2(x_20, x_152, x_151, x_133);
x_154 = l_Lean_Syntax_node2(x_20, x_93, x_153, x_1);
x_155 = l_Lean_Elab_Command_elabCommand(x_154, x_8, x_9, x_92);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_156 = lean_ctor_get(x_21, 0);
x_157 = lean_ctor_get(x_21, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_21);
x_158 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_163 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_20);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_20);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_163);
x_165 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_20);
if (lean_is_scalar(x_161)) {
 x_166 = lean_alloc_ctor(2, 2, 0);
} else {
 x_166 = x_161;
 lean_ctor_set_tag(x_166, 2);
}
lean_ctor_set(x_166, 0, x_20);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_156);
lean_inc(x_159);
x_168 = l_Lean_addMacroScope(x_159, x_167, x_156);
x_169 = lean_box(0);
x_170 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_20);
x_171 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_171, 0, x_20);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
x_172 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_164);
lean_inc(x_20);
x_173 = l_Lean_Syntax_node2(x_20, x_172, x_171, x_164);
x_174 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_20);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_20);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
x_177 = l_Lean_addMacroScope(x_159, x_176, x_156);
x_178 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_179 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_20);
x_180 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_180, 0, x_20);
lean_ctor_set(x_180, 1, x_178);
lean_ctor_set(x_180, 2, x_177);
lean_ctor_set(x_180, 3, x_179);
lean_inc(x_20);
x_181 = l_Lean_Syntax_node1(x_20, x_162, x_2);
x_182 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_20);
x_183 = l_Lean_Syntax_node2(x_20, x_182, x_180, x_181);
x_184 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_20);
x_185 = l_Lean_Syntax_node2(x_20, x_184, x_175, x_183);
lean_inc(x_20);
x_186 = l_Lean_Syntax_node1(x_20, x_162, x_185);
x_187 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_164);
lean_inc(x_20);
x_188 = l_Lean_Syntax_node2(x_20, x_187, x_164, x_186);
x_189 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_20);
lean_ctor_set_tag(x_15, 2);
lean_ctor_set(x_15, 1, x_189);
lean_ctor_set(x_15, 0, x_20);
x_190 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3;
lean_inc(x_20);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_190);
lean_ctor_set(x_11, 0, x_20);
x_191 = lean_mk_syntax_ident(x_6);
x_192 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_20);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_20);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_20);
x_195 = l_Lean_Syntax_node2(x_20, x_194, x_193, x_3);
x_196 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2;
lean_inc(x_164);
lean_inc(x_20);
x_197 = l_Lean_Syntax_node4(x_20, x_196, x_11, x_164, x_191, x_195);
x_198 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_164, 2);
lean_inc(x_20);
x_199 = l_Lean_Syntax_node2(x_20, x_198, x_164, x_164);
x_200 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_164);
lean_inc(x_20);
x_201 = l_Lean_Syntax_node4(x_20, x_200, x_15, x_197, x_199, x_164);
x_202 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_164);
lean_inc(x_20);
x_203 = l_Lean_Syntax_node5(x_20, x_202, x_166, x_173, x_188, x_201, x_164);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_20);
x_205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_205, 0, x_20);
lean_ctor_set(x_205, 1, x_162);
lean_ctor_set(x_205, 2, x_204);
lean_inc_n(x_164, 4);
lean_inc(x_20);
x_206 = l_Lean_Syntax_node6(x_20, x_5, x_164, x_164, x_164, x_164, x_205, x_164);
x_207 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_20);
x_208 = l_Lean_Syntax_node2(x_20, x_207, x_206, x_203);
x_209 = l_Lean_Syntax_node2(x_20, x_162, x_208, x_1);
x_210 = l_Lean_Elab_Command_elabCommand(x_209, x_8, x_9, x_160);
return x_210;
}
else
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_211 = lean_ctor_get(x_4, 0);
x_212 = 1;
x_213 = l_Lean_SourceInfo_fromRef(x_211, x_212);
x_214 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4;
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5;
lean_inc(x_20);
x_217 = l_Lean_Syntax_node1(x_20, x_216, x_215);
x_218 = l_Array_mkArray1___rarg(x_217);
x_219 = l_Array_append___rarg(x_163, x_218);
lean_dec(x_218);
lean_inc(x_20);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_20);
lean_ctor_set(x_220, 1, x_162);
lean_ctor_set(x_220, 2, x_219);
lean_inc_n(x_164, 4);
lean_inc(x_20);
x_221 = l_Lean_Syntax_node6(x_20, x_5, x_164, x_164, x_164, x_164, x_220, x_164);
x_222 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_20);
x_223 = l_Lean_Syntax_node2(x_20, x_222, x_221, x_203);
x_224 = l_Lean_Syntax_node2(x_20, x_162, x_223, x_1);
x_225 = l_Lean_Elab_Command_elabCommand(x_224, x_8, x_9, x_160);
return x_225;
}
}
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_226 = lean_ctor_get(x_15, 0);
x_227 = lean_ctor_get(x_15, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_15);
x_228 = 0;
x_229 = l_Lean_SourceInfo_fromRef(x_226, x_228);
lean_dec(x_226);
x_230 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_9, x_227);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_232);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_239 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_229);
x_240 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_240, 0, x_229);
lean_ctor_set(x_240, 1, x_238);
lean_ctor_set(x_240, 2, x_239);
x_241 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_229);
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(2, 2, 0);
} else {
 x_242 = x_237;
 lean_ctor_set_tag(x_242, 2);
}
lean_ctor_set(x_242, 0, x_229);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_231);
lean_inc(x_235);
x_244 = l_Lean_addMacroScope(x_235, x_243, x_231);
x_245 = lean_box(0);
x_246 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_229);
x_247 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_247, 0, x_229);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set(x_247, 2, x_244);
lean_ctor_set(x_247, 3, x_245);
x_248 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_240);
lean_inc(x_229);
x_249 = l_Lean_Syntax_node2(x_229, x_248, x_247, x_240);
x_250 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_229);
if (lean_is_scalar(x_233)) {
 x_251 = lean_alloc_ctor(2, 2, 0);
} else {
 x_251 = x_233;
 lean_ctor_set_tag(x_251, 2);
}
lean_ctor_set(x_251, 0, x_229);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
x_253 = l_Lean_addMacroScope(x_235, x_252, x_231);
x_254 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_255 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_229);
x_256 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_256, 0, x_229);
lean_ctor_set(x_256, 1, x_254);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_255);
lean_inc(x_229);
x_257 = l_Lean_Syntax_node1(x_229, x_238, x_2);
x_258 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_229);
x_259 = l_Lean_Syntax_node2(x_229, x_258, x_256, x_257);
x_260 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_229);
x_261 = l_Lean_Syntax_node2(x_229, x_260, x_251, x_259);
lean_inc(x_229);
x_262 = l_Lean_Syntax_node1(x_229, x_238, x_261);
x_263 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_240);
lean_inc(x_229);
x_264 = l_Lean_Syntax_node2(x_229, x_263, x_240, x_262);
x_265 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_229);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_229);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3;
lean_inc(x_229);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_267);
lean_ctor_set(x_11, 0, x_229);
x_268 = lean_mk_syntax_ident(x_6);
x_269 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_229);
x_270 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_270, 0, x_229);
lean_ctor_set(x_270, 1, x_269);
x_271 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_229);
x_272 = l_Lean_Syntax_node2(x_229, x_271, x_270, x_3);
x_273 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2;
lean_inc(x_240);
lean_inc(x_229);
x_274 = l_Lean_Syntax_node4(x_229, x_273, x_11, x_240, x_268, x_272);
x_275 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_240, 2);
lean_inc(x_229);
x_276 = l_Lean_Syntax_node2(x_229, x_275, x_240, x_240);
x_277 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_240);
lean_inc(x_229);
x_278 = l_Lean_Syntax_node4(x_229, x_277, x_266, x_274, x_276, x_240);
x_279 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_240);
lean_inc(x_229);
x_280 = l_Lean_Syntax_node5(x_229, x_279, x_242, x_249, x_264, x_278, x_240);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_281 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_229);
x_282 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_282, 0, x_229);
lean_ctor_set(x_282, 1, x_238);
lean_ctor_set(x_282, 2, x_281);
lean_inc_n(x_240, 4);
lean_inc(x_229);
x_283 = l_Lean_Syntax_node6(x_229, x_5, x_240, x_240, x_240, x_240, x_282, x_240);
x_284 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_229);
x_285 = l_Lean_Syntax_node2(x_229, x_284, x_283, x_280);
x_286 = l_Lean_Syntax_node2(x_229, x_238, x_285, x_1);
x_287 = l_Lean_Elab_Command_elabCommand(x_286, x_8, x_9, x_236);
return x_287;
}
else
{
lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_288 = lean_ctor_get(x_4, 0);
x_289 = 1;
x_290 = l_Lean_SourceInfo_fromRef(x_288, x_289);
x_291 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4;
x_292 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5;
lean_inc(x_229);
x_294 = l_Lean_Syntax_node1(x_229, x_293, x_292);
x_295 = l_Array_mkArray1___rarg(x_294);
x_296 = l_Array_append___rarg(x_239, x_295);
lean_dec(x_295);
lean_inc(x_229);
x_297 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_297, 0, x_229);
lean_ctor_set(x_297, 1, x_238);
lean_ctor_set(x_297, 2, x_296);
lean_inc_n(x_240, 4);
lean_inc(x_229);
x_298 = l_Lean_Syntax_node6(x_229, x_5, x_240, x_240, x_240, x_240, x_297, x_240);
x_299 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_229);
x_300 = l_Lean_Syntax_node2(x_229, x_299, x_298, x_280);
x_301 = l_Lean_Syntax_node2(x_229, x_238, x_300, x_1);
x_302 = l_Lean_Elab_Command_elabCommand(x_301, x_8, x_9, x_236);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_303 = lean_ctor_get(x_11, 1);
lean_inc(x_303);
lean_dec(x_11);
x_304 = l_Lean_Elab_Command_getRef(x_8, x_9, x_303);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_307 = x_304;
} else {
 lean_dec_ref(x_304);
 x_307 = lean_box(0);
}
x_308 = 0;
x_309 = l_Lean_SourceInfo_fromRef(x_305, x_308);
lean_dec(x_305);
x_310 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_9, x_306);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_313 = x_310;
} else {
 lean_dec_ref(x_310);
 x_313 = lean_box(0);
}
x_314 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_312);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_317 = x_314;
} else {
 lean_dec_ref(x_314);
 x_317 = lean_box(0);
}
x_318 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_319 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_309);
x_320 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_320, 0, x_309);
lean_ctor_set(x_320, 1, x_318);
lean_ctor_set(x_320, 2, x_319);
x_321 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14;
lean_inc(x_309);
if (lean_is_scalar(x_317)) {
 x_322 = lean_alloc_ctor(2, 2, 0);
} else {
 x_322 = x_317;
 lean_ctor_set_tag(x_322, 2);
}
lean_ctor_set(x_322, 0, x_309);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
lean_inc(x_311);
lean_inc(x_315);
x_324 = l_Lean_addMacroScope(x_315, x_323, x_311);
x_325 = lean_box(0);
x_326 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_309);
x_327 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_327, 0, x_309);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_327, 2, x_324);
lean_ctor_set(x_327, 3, x_325);
x_328 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
lean_inc(x_320);
lean_inc(x_309);
x_329 = l_Lean_Syntax_node2(x_309, x_328, x_327, x_320);
x_330 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_309);
if (lean_is_scalar(x_313)) {
 x_331 = lean_alloc_ctor(2, 2, 0);
} else {
 x_331 = x_313;
 lean_ctor_set_tag(x_331, 2);
}
lean_ctor_set(x_331, 0, x_309);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29;
x_333 = l_Lean_addMacroScope(x_315, x_332, x_311);
x_334 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28;
x_335 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33;
lean_inc(x_309);
x_336 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_336, 0, x_309);
lean_ctor_set(x_336, 1, x_334);
lean_ctor_set(x_336, 2, x_333);
lean_ctor_set(x_336, 3, x_335);
lean_inc(x_309);
x_337 = l_Lean_Syntax_node1(x_309, x_318, x_2);
x_338 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26;
lean_inc(x_309);
x_339 = l_Lean_Syntax_node2(x_309, x_338, x_336, x_337);
x_340 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_309);
x_341 = l_Lean_Syntax_node2(x_309, x_340, x_331, x_339);
lean_inc(x_309);
x_342 = l_Lean_Syntax_node1(x_309, x_318, x_341);
x_343 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21;
lean_inc(x_320);
lean_inc(x_309);
x_344 = l_Lean_Syntax_node2(x_309, x_343, x_320, x_342);
x_345 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1;
lean_inc(x_309);
if (lean_is_scalar(x_307)) {
 x_346 = lean_alloc_ctor(2, 2, 0);
} else {
 x_346 = x_307;
 lean_ctor_set_tag(x_346, 2);
}
lean_ctor_set(x_346, 0, x_309);
lean_ctor_set(x_346, 1, x_345);
x_347 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3;
lean_inc(x_309);
x_348 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_348, 0, x_309);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_mk_syntax_ident(x_6);
x_350 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43;
lean_inc(x_309);
x_351 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_351, 0, x_309);
lean_ctor_set(x_351, 1, x_350);
x_352 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44;
lean_inc(x_309);
x_353 = l_Lean_Syntax_node2(x_309, x_352, x_351, x_3);
x_354 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2;
lean_inc(x_320);
lean_inc(x_309);
x_355 = l_Lean_Syntax_node4(x_309, x_354, x_348, x_320, x_349, x_353);
x_356 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47;
lean_inc_n(x_320, 2);
lean_inc(x_309);
x_357 = l_Lean_Syntax_node2(x_309, x_356, x_320, x_320);
x_358 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42;
lean_inc(x_320);
lean_inc(x_309);
x_359 = l_Lean_Syntax_node4(x_309, x_358, x_346, x_355, x_357, x_320);
x_360 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9;
lean_inc(x_320);
lean_inc(x_309);
x_361 = l_Lean_Syntax_node5(x_309, x_360, x_322, x_329, x_344, x_359, x_320);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_362 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_309);
x_363 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_363, 0, x_309);
lean_ctor_set(x_363, 1, x_318);
lean_ctor_set(x_363, 2, x_362);
lean_inc_n(x_320, 4);
lean_inc(x_309);
x_364 = l_Lean_Syntax_node6(x_309, x_5, x_320, x_320, x_320, x_320, x_363, x_320);
x_365 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_309);
x_366 = l_Lean_Syntax_node2(x_309, x_365, x_364, x_361);
x_367 = l_Lean_Syntax_node2(x_309, x_318, x_366, x_1);
x_368 = l_Lean_Elab_Command_elabCommand(x_367, x_8, x_9, x_316);
return x_368;
}
else
{
lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_369 = lean_ctor_get(x_4, 0);
x_370 = 1;
x_371 = l_Lean_SourceInfo_fromRef(x_369, x_370);
x_372 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4;
x_373 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
x_374 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5;
lean_inc(x_309);
x_375 = l_Lean_Syntax_node1(x_309, x_374, x_373);
x_376 = l_Array_mkArray1___rarg(x_375);
x_377 = l_Array_append___rarg(x_319, x_376);
lean_dec(x_376);
lean_inc(x_309);
x_378 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_378, 0, x_309);
lean_ctor_set(x_378, 1, x_318);
lean_ctor_set(x_378, 2, x_377);
lean_inc_n(x_320, 4);
lean_inc(x_309);
x_379 = l_Lean_Syntax_node6(x_309, x_5, x_320, x_320, x_320, x_320, x_378, x_320);
x_380 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
lean_inc(x_309);
x_381 = l_Lean_Syntax_node2(x_309, x_380, x_379, x_361);
x_382 = l_Lean_Syntax_node2(x_309, x_318, x_381, x_1);
x_383 = l_Lean_Elab_Command_elabCommand(x_382, x_8, x_9, x_316);
return x_383;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("private", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_3 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declSig", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_324 = lean_unsigned_to_nat(5u);
x_325 = l_Lean_Syntax_getArg(x_8, x_324);
x_326 = lean_unsigned_to_nat(0u);
x_327 = l_Lean_Syntax_matchesNull(x_325, x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_328 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_329 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_8, x_328, x_12, x_13, x_14);
lean_dec(x_13);
return x_329;
}
else
{
lean_object* x_330; 
x_330 = l_Lean_Syntax_getOptional_x3f(x_9);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; 
x_331 = lean_box(0);
x_15 = x_331;
goto block_323;
}
else
{
uint8_t x_332; 
x_332 = !lean_is_exclusive(x_330);
if (x_332 == 0)
{
x_15 = x_330;
goto block_323;
}
else
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_dec(x_330);
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_333);
x_15 = x_334;
goto block_323;
}
}
}
block_323:
{
lean_object* x_16; lean_object* x_17; lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Elab_Command_getRef(x_12, x_13, x_14);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = 0;
x_44 = l_Lean_SourceInfo_fromRef(x_41, x_43);
lean_dec(x_41);
x_45 = l_Lean_Elab_Command_getCurrMacroScope(x_12, x_13, x_42);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = l_Lean_Elab_Command_getMainModule___rarg(x_13, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_53 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
lean_inc(x_44);
lean_ctor_set_tag(x_49, 2);
lean_ctor_set(x_49, 1, x_53);
lean_ctor_set(x_49, 0, x_44);
x_54 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_55 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_44);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_55);
x_57 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_inc(x_56);
lean_inc(x_44);
x_58 = l_Lean_Syntax_node1(x_44, x_57, x_56);
x_59 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
x_60 = l_Lean_addMacroScope(x_51, x_59, x_47);
x_61 = lean_box(0);
x_62 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_44);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_44);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_61);
lean_inc(x_44);
x_64 = l_Lean_Syntax_node1(x_44, x_54, x_63);
x_65 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_inc(x_44);
x_66 = l_Lean_Syntax_node2(x_44, x_65, x_5, x_64);
x_67 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
lean_inc(x_44);
x_68 = l_Lean_Syntax_node2(x_44, x_67, x_58, x_66);
x_69 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3;
lean_inc(x_44);
lean_ctor_set_tag(x_45, 2);
lean_ctor_set(x_45, 1, x_69);
lean_ctor_set(x_45, 0, x_44);
x_70 = l_Array_mkArray2___rarg(x_68, x_45);
x_71 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_inc(x_44);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_71);
lean_ctor_set(x_39, 0, x_44);
x_72 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12;
lean_inc(x_44);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_44);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5;
lean_inc(x_1);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_mk(x_75);
x_77 = lean_box(2);
x_78 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_76);
x_80 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_44);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_44);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_2);
lean_inc(x_44);
x_83 = l_Lean_Syntax_node2(x_44, x_82, x_81, x_2);
x_84 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7;
lean_inc(x_56);
lean_inc(x_44);
x_85 = l_Lean_Syntax_node2(x_44, x_84, x_56, x_83);
x_86 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13;
lean_inc(x_56);
lean_inc(x_44);
x_87 = l_Lean_Syntax_node4(x_44, x_86, x_73, x_79, x_85, x_56);
if (lean_obj_tag(x_7) == 0)
{
x_88 = x_55;
goto block_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_7, 0);
lean_inc(x_112);
lean_dec(x_7);
x_113 = l_Array_mkArray1___rarg(x_112);
x_88 = x_113;
goto block_111;
}
block_111:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = l_Array_append___rarg(x_55, x_88);
lean_dec(x_88);
lean_inc(x_44);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_44);
lean_ctor_set(x_90, 1, x_54);
lean_ctor_set(x_90, 2, x_89);
if (lean_obj_tag(x_6) == 0)
{
x_91 = x_55;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_6, 0);
lean_inc(x_110);
lean_dec(x_6);
x_91 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = l_Array_append___rarg(x_70, x_91);
lean_dec(x_91);
lean_inc(x_44);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_44);
lean_ctor_set(x_93, 1, x_54);
lean_ctor_set(x_93, 2, x_92);
x_94 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_44);
x_95 = l_Lean_Syntax_node3(x_44, x_94, x_49, x_93, x_39);
lean_inc(x_44);
x_96 = l_Lean_Syntax_node1(x_44, x_54, x_95);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_44);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_44);
lean_ctor_set(x_98, 1, x_54);
lean_ctor_set(x_98, 2, x_97);
lean_inc_n(x_56, 2);
lean_inc(x_4);
lean_inc(x_44);
x_99 = l_Lean_Syntax_node6(x_44, x_4, x_90, x_96, x_98, x_56, x_56, x_56);
x_100 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_101 = l_Lean_Syntax_node2(x_44, x_100, x_99, x_87);
x_16 = x_101;
x_17 = x_52;
goto block_38;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_15, 0);
lean_inc(x_102);
x_103 = lean_array_push(x_55, x_102);
x_104 = l_Array_append___rarg(x_55, x_103);
lean_dec(x_103);
lean_inc(x_44);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_44);
lean_ctor_set(x_105, 1, x_54);
lean_ctor_set(x_105, 2, x_104);
lean_inc_n(x_56, 2);
lean_inc(x_4);
lean_inc(x_44);
x_106 = l_Lean_Syntax_node6(x_44, x_4, x_90, x_96, x_105, x_56, x_56, x_56);
x_107 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_108 = l_Lean_Syntax_node2(x_44, x_107, x_106, x_87);
x_16 = x_108;
x_17 = x_52;
goto block_38;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_114 = lean_ctor_get(x_49, 0);
x_115 = lean_ctor_get(x_49, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_49);
x_116 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
lean_inc(x_44);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_44);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_119 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_44);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_44);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_119);
x_121 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_inc(x_120);
lean_inc(x_44);
x_122 = l_Lean_Syntax_node1(x_44, x_121, x_120);
x_123 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
x_124 = l_Lean_addMacroScope(x_114, x_123, x_47);
x_125 = lean_box(0);
x_126 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_44);
x_127 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_127, 0, x_44);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_124);
lean_ctor_set(x_127, 3, x_125);
lean_inc(x_44);
x_128 = l_Lean_Syntax_node1(x_44, x_118, x_127);
x_129 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_inc(x_44);
x_130 = l_Lean_Syntax_node2(x_44, x_129, x_5, x_128);
x_131 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
lean_inc(x_44);
x_132 = l_Lean_Syntax_node2(x_44, x_131, x_122, x_130);
x_133 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3;
lean_inc(x_44);
lean_ctor_set_tag(x_45, 2);
lean_ctor_set(x_45, 1, x_133);
lean_ctor_set(x_45, 0, x_44);
x_134 = l_Array_mkArray2___rarg(x_132, x_45);
x_135 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_inc(x_44);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_44);
x_136 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12;
lean_inc(x_44);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_44);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5;
lean_inc(x_1);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_array_mk(x_139);
x_141 = lean_box(2);
x_142 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
x_143 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_140);
x_144 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_44);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_44);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_2);
lean_inc(x_44);
x_147 = l_Lean_Syntax_node2(x_44, x_146, x_145, x_2);
x_148 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7;
lean_inc(x_120);
lean_inc(x_44);
x_149 = l_Lean_Syntax_node2(x_44, x_148, x_120, x_147);
x_150 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13;
lean_inc(x_120);
lean_inc(x_44);
x_151 = l_Lean_Syntax_node4(x_44, x_150, x_137, x_143, x_149, x_120);
if (lean_obj_tag(x_7) == 0)
{
x_152 = x_119;
goto block_175;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_7, 0);
lean_inc(x_176);
lean_dec(x_7);
x_177 = l_Array_mkArray1___rarg(x_176);
x_152 = x_177;
goto block_175;
}
block_175:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = l_Array_append___rarg(x_119, x_152);
lean_dec(x_152);
lean_inc(x_44);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_44);
lean_ctor_set(x_154, 1, x_118);
lean_ctor_set(x_154, 2, x_153);
if (lean_obj_tag(x_6) == 0)
{
x_155 = x_119;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_6, 0);
lean_inc(x_174);
lean_dec(x_6);
x_155 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = l_Array_append___rarg(x_134, x_155);
lean_dec(x_155);
lean_inc(x_44);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_44);
lean_ctor_set(x_157, 1, x_118);
lean_ctor_set(x_157, 2, x_156);
x_158 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_44);
x_159 = l_Lean_Syntax_node3(x_44, x_158, x_117, x_157, x_39);
lean_inc(x_44);
x_160 = l_Lean_Syntax_node1(x_44, x_118, x_159);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_44);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_44);
lean_ctor_set(x_162, 1, x_118);
lean_ctor_set(x_162, 2, x_161);
lean_inc_n(x_120, 2);
lean_inc(x_4);
lean_inc(x_44);
x_163 = l_Lean_Syntax_node6(x_44, x_4, x_154, x_160, x_162, x_120, x_120, x_120);
x_164 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_165 = l_Lean_Syntax_node2(x_44, x_164, x_163, x_151);
x_16 = x_165;
x_17 = x_115;
goto block_38;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_15, 0);
lean_inc(x_166);
x_167 = lean_array_push(x_119, x_166);
x_168 = l_Array_append___rarg(x_119, x_167);
lean_dec(x_167);
lean_inc(x_44);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_44);
lean_ctor_set(x_169, 1, x_118);
lean_ctor_set(x_169, 2, x_168);
lean_inc_n(x_120, 2);
lean_inc(x_4);
lean_inc(x_44);
x_170 = l_Lean_Syntax_node6(x_44, x_4, x_154, x_160, x_169, x_120, x_120, x_120);
x_171 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_172 = l_Lean_Syntax_node2(x_44, x_171, x_170, x_151);
x_16 = x_172;
x_17 = x_115;
goto block_38;
}
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_178 = lean_ctor_get(x_45, 0);
x_179 = lean_ctor_get(x_45, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_45);
x_180 = l_Lean_Elab_Command_getMainModule___rarg(x_13, x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
lean_inc(x_44);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(2, 2, 0);
} else {
 x_185 = x_183;
 lean_ctor_set_tag(x_185, 2);
}
lean_ctor_set(x_185, 0, x_44);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_187 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_44);
x_188 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_188, 0, x_44);
lean_ctor_set(x_188, 1, x_186);
lean_ctor_set(x_188, 2, x_187);
x_189 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_inc(x_188);
lean_inc(x_44);
x_190 = l_Lean_Syntax_node1(x_44, x_189, x_188);
x_191 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
x_192 = l_Lean_addMacroScope(x_181, x_191, x_178);
x_193 = lean_box(0);
x_194 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_44);
x_195 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_195, 0, x_44);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_192);
lean_ctor_set(x_195, 3, x_193);
lean_inc(x_44);
x_196 = l_Lean_Syntax_node1(x_44, x_186, x_195);
x_197 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_inc(x_44);
x_198 = l_Lean_Syntax_node2(x_44, x_197, x_5, x_196);
x_199 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
lean_inc(x_44);
x_200 = l_Lean_Syntax_node2(x_44, x_199, x_190, x_198);
x_201 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3;
lean_inc(x_44);
x_202 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_202, 0, x_44);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Array_mkArray2___rarg(x_200, x_202);
x_204 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_inc(x_44);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_204);
lean_ctor_set(x_39, 0, x_44);
x_205 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12;
lean_inc(x_44);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_44);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5;
lean_inc(x_1);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_1);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_array_mk(x_208);
x_210 = lean_box(2);
x_211 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_209);
x_213 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_44);
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_44);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_2);
lean_inc(x_44);
x_216 = l_Lean_Syntax_node2(x_44, x_215, x_214, x_2);
x_217 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7;
lean_inc(x_188);
lean_inc(x_44);
x_218 = l_Lean_Syntax_node2(x_44, x_217, x_188, x_216);
x_219 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13;
lean_inc(x_188);
lean_inc(x_44);
x_220 = l_Lean_Syntax_node4(x_44, x_219, x_206, x_212, x_218, x_188);
if (lean_obj_tag(x_7) == 0)
{
x_221 = x_187;
goto block_244;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_7, 0);
lean_inc(x_245);
lean_dec(x_7);
x_246 = l_Array_mkArray1___rarg(x_245);
x_221 = x_246;
goto block_244;
}
block_244:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = l_Array_append___rarg(x_187, x_221);
lean_dec(x_221);
lean_inc(x_44);
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_44);
lean_ctor_set(x_223, 1, x_186);
lean_ctor_set(x_223, 2, x_222);
if (lean_obj_tag(x_6) == 0)
{
x_224 = x_187;
goto block_242;
}
else
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_6, 0);
lean_inc(x_243);
lean_dec(x_6);
x_224 = x_243;
goto block_242;
}
block_242:
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = l_Array_append___rarg(x_203, x_224);
lean_dec(x_224);
lean_inc(x_44);
x_226 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_226, 0, x_44);
lean_ctor_set(x_226, 1, x_186);
lean_ctor_set(x_226, 2, x_225);
x_227 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_44);
x_228 = l_Lean_Syntax_node3(x_44, x_227, x_185, x_226, x_39);
lean_inc(x_44);
x_229 = l_Lean_Syntax_node1(x_44, x_186, x_228);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_230 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_44);
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_44);
lean_ctor_set(x_231, 1, x_186);
lean_ctor_set(x_231, 2, x_230);
lean_inc_n(x_188, 2);
lean_inc(x_4);
lean_inc(x_44);
x_232 = l_Lean_Syntax_node6(x_44, x_4, x_223, x_229, x_231, x_188, x_188, x_188);
x_233 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_234 = l_Lean_Syntax_node2(x_44, x_233, x_232, x_220);
x_16 = x_234;
x_17 = x_182;
goto block_38;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_235 = lean_ctor_get(x_15, 0);
lean_inc(x_235);
x_236 = lean_array_push(x_187, x_235);
x_237 = l_Array_append___rarg(x_187, x_236);
lean_dec(x_236);
lean_inc(x_44);
x_238 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_238, 0, x_44);
lean_ctor_set(x_238, 1, x_186);
lean_ctor_set(x_238, 2, x_237);
lean_inc_n(x_188, 2);
lean_inc(x_4);
lean_inc(x_44);
x_239 = l_Lean_Syntax_node6(x_44, x_4, x_223, x_229, x_238, x_188, x_188, x_188);
x_240 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_241 = l_Lean_Syntax_node2(x_44, x_240, x_239, x_220);
x_16 = x_241;
x_17 = x_182;
goto block_38;
}
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_247 = lean_ctor_get(x_39, 0);
x_248 = lean_ctor_get(x_39, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_39);
x_249 = 0;
x_250 = l_Lean_SourceInfo_fromRef(x_247, x_249);
lean_dec(x_247);
x_251 = l_Lean_Elab_Command_getCurrMacroScope(x_12, x_13, x_248);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_255 = l_Lean_Elab_Command_getMainModule___rarg(x_13, x_253);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
x_259 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6;
lean_inc(x_250);
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(2, 2, 0);
} else {
 x_260 = x_258;
 lean_ctor_set_tag(x_260, 2);
}
lean_ctor_set(x_260, 0, x_250);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2;
x_262 = l_Lean_Elab_Command_expandMutualPreamble___closed__3;
lean_inc(x_250);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_250);
lean_ctor_set(x_263, 1, x_261);
lean_ctor_set(x_263, 2, x_262);
x_264 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10;
lean_inc(x_263);
lean_inc(x_250);
x_265 = l_Lean_Syntax_node1(x_250, x_264, x_263);
x_266 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19;
x_267 = l_Lean_addMacroScope(x_256, x_266, x_252);
x_268 = lean_box(0);
x_269 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18;
lean_inc(x_250);
x_270 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_270, 0, x_250);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set(x_270, 2, x_267);
lean_ctor_set(x_270, 3, x_268);
lean_inc(x_250);
x_271 = l_Lean_Syntax_node1(x_250, x_261, x_270);
x_272 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13;
lean_inc(x_250);
x_273 = l_Lean_Syntax_node2(x_250, x_272, x_5, x_271);
x_274 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8;
lean_inc(x_250);
x_275 = l_Lean_Syntax_node2(x_250, x_274, x_265, x_273);
x_276 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3;
lean_inc(x_250);
if (lean_is_scalar(x_254)) {
 x_277 = lean_alloc_ctor(2, 2, 0);
} else {
 x_277 = x_254;
 lean_ctor_set_tag(x_277, 2);
}
lean_ctor_set(x_277, 0, x_250);
lean_ctor_set(x_277, 1, x_276);
x_278 = l_Array_mkArray2___rarg(x_275, x_277);
x_279 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5;
lean_inc(x_250);
x_280 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_280, 0, x_250);
lean_ctor_set(x_280, 1, x_279);
x_281 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12;
lean_inc(x_250);
x_282 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_282, 0, x_250);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5;
lean_inc(x_1);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_1);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_array_mk(x_284);
x_286 = lean_box(2);
x_287 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16;
x_288 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_288, 2, x_285);
x_289 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24;
lean_inc(x_250);
x_290 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_290, 0, x_250);
lean_ctor_set(x_290, 1, x_289);
x_291 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_2);
lean_inc(x_250);
x_292 = l_Lean_Syntax_node2(x_250, x_291, x_290, x_2);
x_293 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7;
lean_inc(x_263);
lean_inc(x_250);
x_294 = l_Lean_Syntax_node2(x_250, x_293, x_263, x_292);
x_295 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13;
lean_inc(x_263);
lean_inc(x_250);
x_296 = l_Lean_Syntax_node4(x_250, x_295, x_282, x_288, x_294, x_263);
if (lean_obj_tag(x_7) == 0)
{
x_297 = x_262;
goto block_320;
}
else
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_7, 0);
lean_inc(x_321);
lean_dec(x_7);
x_322 = l_Array_mkArray1___rarg(x_321);
x_297 = x_322;
goto block_320;
}
block_320:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = l_Array_append___rarg(x_262, x_297);
lean_dec(x_297);
lean_inc(x_250);
x_299 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_299, 0, x_250);
lean_ctor_set(x_299, 1, x_261);
lean_ctor_set(x_299, 2, x_298);
if (lean_obj_tag(x_6) == 0)
{
x_300 = x_262;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_6, 0);
lean_inc(x_319);
lean_dec(x_6);
x_300 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_301 = l_Array_append___rarg(x_278, x_300);
lean_dec(x_300);
lean_inc(x_250);
x_302 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_302, 0, x_250);
lean_ctor_set(x_302, 1, x_261);
lean_ctor_set(x_302, 2, x_301);
x_303 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_250);
x_304 = l_Lean_Syntax_node3(x_250, x_303, x_260, x_302, x_280);
lean_inc(x_250);
x_305 = l_Lean_Syntax_node1(x_250, x_261, x_304);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_306 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48;
lean_inc(x_250);
x_307 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_307, 0, x_250);
lean_ctor_set(x_307, 1, x_261);
lean_ctor_set(x_307, 2, x_306);
lean_inc_n(x_263, 2);
lean_inc(x_4);
lean_inc(x_250);
x_308 = l_Lean_Syntax_node6(x_250, x_4, x_299, x_305, x_307, x_263, x_263, x_263);
x_309 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_310 = l_Lean_Syntax_node2(x_250, x_309, x_308, x_296);
x_16 = x_310;
x_17 = x_257;
goto block_38;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_311 = lean_ctor_get(x_15, 0);
lean_inc(x_311);
x_312 = lean_array_push(x_262, x_311);
x_313 = l_Array_append___rarg(x_262, x_312);
lean_dec(x_312);
lean_inc(x_250);
x_314 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_314, 0, x_250);
lean_ctor_set(x_314, 1, x_261);
lean_ctor_set(x_314, 2, x_313);
lean_inc_n(x_263, 2);
lean_inc(x_4);
lean_inc(x_250);
x_315 = l_Lean_Syntax_node6(x_250, x_4, x_299, x_305, x_314, x_263, x_263, x_263);
x_316 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5;
x_317 = l_Lean_Syntax_node2(x_250, x_316, x_315, x_296);
x_16 = x_317;
x_17 = x_257;
goto block_38;
}
}
}
}
block_38:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_Elab_Command_getScope___rarg(x_13, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_23 = l_Lean_Name_append(x_21, x_22);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Command_elabInitialize___lambda__2(x_16, x_2, x_3, x_11, x_4, x_23, x_24, x_12, x_13, x_20);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = l_Lean_Elab_Command_elabInitialize___lambda__3___closed__2;
x_28 = l_Lean_Syntax_isOfKind(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Command_elabInitialize___lambda__2(x_16, x_2, x_3, x_11, x_4, x_23, x_29, x_12, x_13, x_20);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_st_ref_get(x_13, x_20);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_mkPrivateName(x_34, x_23);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Command_elabInitialize___lambda__2(x_16, x_2, x_3, x_11, x_4, x_35, x_36, x_12, x_13, x_33);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_matchesNull(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_20 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_19, x_10, x_11, x_12);
lean_dec(x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_22);
x_25 = l_Lean_Syntax_matchesNull(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_27 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_26, x_10, x_11, x_12);
lean_dec(x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Syntax_getArg(x_22, x_17);
lean_dec(x_22);
x_29 = l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5;
lean_inc(x_28);
x_30 = l_Lean_Syntax_isOfKind(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_32 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_31, x_10, x_11, x_12);
lean_dec(x_11);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l_Lean_Syntax_getArg(x_28, x_17);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Command_elabInitialize___lambda__3(x_2, x_3, x_4, x_5, x_6, x_9, x_7, x_1, x_14, x_35, x_34, x_10, x_11, x_12);
lean_dec(x_34);
lean_dec(x_14);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_22);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Command_elabInitialize___lambda__3(x_2, x_3, x_4, x_5, x_6, x_9, x_7, x_1, x_14, x_38, x_37, x_10, x_11, x_12);
lean_dec(x_14);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_isNone(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_13);
x_15 = l_Lean_Syntax_matchesNull(x_13, x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_17 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_16, x_9, x_10, x_11);
lean_dec(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
lean_dec(x_13);
x_20 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5;
lean_inc(x_19);
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_23 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_1, x_22, x_9, x_10, x_11);
lean_dec(x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = l_Lean_Syntax_getArg(x_19, x_12);
lean_dec(x_19);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Command_elabInitialize___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_27, x_26, x_9, x_10, x_11);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Command_elabInitialize___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_30, x_29, x_9, x_10, x_11);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("docComment", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initialize", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("builtin_init", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Lean_Syntax_getArg(x_4, x_111);
x_113 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__3;
x_114 = l_Lean_Syntax_isToken(x_113, x_112);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__5;
x_13 = x_115;
goto block_110;
}
else
{
lean_object* x_116; 
x_116 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__7;
x_13 = x_116;
goto block_110;
}
block_110:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
x_15 = l_Lean_mkIdentFrom(x_1, x_13, x_14);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_2, x_16);
x_18 = l_Lean_Syntax_isNone(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(1u);
lean_inc(x_17);
x_20 = l_Lean_Syntax_matchesNull(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_21 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_22 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_21, x_8, x_9, x_10);
lean_dec(x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Syntax_getArg(x_17, x_16);
lean_dec(x_17);
x_24 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2;
lean_inc(x_23);
x_25 = l_Lean_Syntax_isOfKind(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_26 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_27 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_26, x_8, x_9, x_10);
lean_dec(x_9);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Command_elabInitialize___lambda__1(x_2, x_15, x_12, x_3, x_29, x_28, x_8, x_9, x_10);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_17);
x_31 = lean_box(0);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Command_elabInitialize___lambda__1(x_2, x_15, x_12, x_3, x_32, x_31, x_8, x_9, x_10);
return x_33;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_6, 0);
lean_dec(x_35);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Syntax_getArg(x_2, x_36);
x_38 = l_Lean_Syntax_isNone(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1u);
lean_inc(x_37);
x_40 = l_Lean_Syntax_matchesNull(x_37, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_41 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_42 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_41, x_8, x_9, x_10);
lean_dec(x_9);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Syntax_getArg(x_37, x_36);
lean_dec(x_37);
x_44 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2;
lean_inc(x_43);
x_45 = l_Lean_Syntax_isOfKind(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_46 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_47 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_46, x_8, x_9, x_10);
lean_dec(x_9);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_ctor_set(x_6, 0, x_43);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Command_elabInitialize___lambda__1(x_2, x_15, x_12, x_3, x_48, x_6, x_8, x_9, x_10);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
lean_free_object(x_6);
x_50 = lean_box(0);
x_51 = lean_box(0);
x_52 = l_Lean_Elab_Command_elabInitialize___lambda__1(x_2, x_15, x_12, x_3, x_51, x_50, x_8, x_9, x_10);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_6);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lean_Syntax_getArg(x_2, x_53);
x_55 = l_Lean_Syntax_isNone(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_unsigned_to_nat(1u);
lean_inc(x_54);
x_57 = l_Lean_Syntax_matchesNull(x_54, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_58 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_59 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_58, x_8, x_9, x_10);
lean_dec(x_9);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = l_Lean_Syntax_getArg(x_54, x_53);
lean_dec(x_54);
x_61 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2;
lean_inc(x_60);
x_62 = l_Lean_Syntax_isOfKind(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_63 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_64 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_63, x_8, x_9, x_10);
lean_dec(x_9);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_66 = lean_box(0);
x_67 = l_Lean_Elab_Command_elabInitialize___lambda__1(x_2, x_15, x_12, x_3, x_66, x_65, x_8, x_9, x_10);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
x_68 = lean_box(0);
x_69 = lean_box(0);
x_70 = l_Lean_Elab_Command_elabInitialize___lambda__1(x_2, x_15, x_12, x_3, x_69, x_68, x_8, x_9, x_10);
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_6, 0);
lean_inc(x_71);
lean_dec(x_6);
x_72 = !lean_is_exclusive(x_7);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_7, 0);
x_74 = lean_unsigned_to_nat(0u);
x_75 = l_Lean_Syntax_getArg(x_2, x_74);
x_76 = l_Lean_Syntax_isNone(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_unsigned_to_nat(1u);
lean_inc(x_75);
x_78 = l_Lean_Syntax_matchesNull(x_75, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_75);
lean_free_object(x_7);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_79 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_80 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_79, x_8, x_9, x_10);
lean_dec(x_9);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = l_Lean_Syntax_getArg(x_75, x_74);
lean_dec(x_75);
x_82 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2;
lean_inc(x_81);
x_83 = l_Lean_Syntax_isOfKind(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_free_object(x_7);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_84 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_85 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_84, x_8, x_9, x_10);
lean_dec(x_9);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_ctor_set(x_7, 0, x_81);
x_86 = lean_box(0);
x_87 = l_Lean_Elab_Command_elabInitialize___lambda__5(x_2, x_71, x_73, x_12, x_3, x_15, x_86, x_7, x_8, x_9, x_10);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_free_object(x_7);
x_88 = lean_box(0);
x_89 = lean_box(0);
x_90 = l_Lean_Elab_Command_elabInitialize___lambda__5(x_2, x_71, x_73, x_12, x_3, x_15, x_89, x_88, x_8, x_9, x_10);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_7, 0);
lean_inc(x_91);
lean_dec(x_7);
x_92 = lean_unsigned_to_nat(0u);
x_93 = l_Lean_Syntax_getArg(x_2, x_92);
x_94 = l_Lean_Syntax_isNone(x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_unsigned_to_nat(1u);
lean_inc(x_93);
x_96 = l_Lean_Syntax_matchesNull(x_93, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_71);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_97 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_98 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_97, x_8, x_9, x_10);
lean_dec(x_9);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = l_Lean_Syntax_getArg(x_93, x_92);
lean_dec(x_93);
x_100 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2;
lean_inc(x_99);
x_101 = l_Lean_Syntax_isOfKind(x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_99);
lean_dec(x_91);
lean_dec(x_71);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_102 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2;
x_103 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_Doc_elabTacticExtension___spec__2(x_2, x_102, x_8, x_9, x_10);
lean_dec(x_9);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_105 = lean_box(0);
x_106 = l_Lean_Elab_Command_elabInitialize___lambda__5(x_2, x_71, x_91, x_12, x_3, x_15, x_105, x_104, x_8, x_9, x_10);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_93);
x_107 = lean_box(0);
x_108 = lean_box(0);
x_109 = l_Lean_Elab_Command_elabInitialize___lambda__5(x_2, x_71, x_91, x_12, x_3, x_15, x_108, x_107, x_8, x_9, x_10);
return x_109;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___lambda__6___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declModifiers", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initializeKeyword", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInitialize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l_Lean_Elab_Command_elabInitialize___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabInitialize___closed__1;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Elab_Command_elabInitialize___closed__3;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Elab_Command_elabInitialize___closed__5;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_isNone(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(3u);
lean_inc(x_19);
x_22 = l_Lean_Syntax_matchesNull(x_19, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Syntax_getArg(x_19, x_8);
x_25 = l_Lean_Syntax_getArg(x_19, x_13);
lean_dec(x_19);
x_26 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23;
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabSyntax___spec__1___rarg(x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_Syntax_getArg(x_25, x_13);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_24);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Command_elabInitialize___lambda__6(x_1, x_9, x_10, x_14, x_32, x_30, x_31, x_2, x_3, x_4);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_1);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Command_elabInitialize___lambda__6(x_1, x_9, x_10, x_14, x_35, x_34, x_34, x_2, x_3, x_4);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_1);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabInitialize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabInitialize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_elabInitialize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Command_elabInitialize___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabInitialize___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitialize___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabInitialize___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabInitialize", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitialize), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabInitialize__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3;
x_3 = l_Lean_Elab_Command_elabInitialize___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__1;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__2;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__3;
x_2 = l_Lean_Elab_Command_elabInitialize___lambda__1___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__4;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__6;
x_2 = l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__7;
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Declaration", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__8;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__10;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__12;
x_2 = lean_unsigned_to_nat(9024u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7;
x_3 = 0;
x_4 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__13;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DefView(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Inductive(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MutualDef(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Declaration(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__4);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__5 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_ensureValidNamespace___closed__5);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__4);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__5 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__5);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__6 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__6);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__7 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDeclIdName___closed__7);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__4);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__5);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__6 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__6);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__7 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__7);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__8 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__8);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__9);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__10 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__10);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__11 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__11);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__12);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__13);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__14 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__14);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__15 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__15);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__16 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__16);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__17 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__17);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__18 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__18);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__19 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__19);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__20 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__20);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__21 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isNamedDef___closed__21);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isInstanceDef___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_setDefName___closed__4);
l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1 = _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1();
lean_mark_persistent(l_Lean_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__3___closed__1);
l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1 = _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__1);
l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2 = _init_l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___at_Lean_Elab_Command_elabAxiom___spec__1___closed__2);
l_Lean_Elab_Command_elabAxiom___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabAxiom___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__3___closed__1);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__1 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__1);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__2 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__2);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__3 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__3);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__4);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__5 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__5);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__6);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__7);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__8 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__8);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__9);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__10 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__10);
l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11 = _init_l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabAxiom___lambda__4___closed__11);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___lambda__3___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__1___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___lambda__3___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__3___closed__3);
l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__1 = _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__1();
lean_mark_persistent(l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__1);
l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__2 = _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__2();
lean_mark_persistent(l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__2);
l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__3 = _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__3();
lean_mark_persistent(l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__3);
l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__4 = _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__4();
lean_mark_persistent(l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__4);
l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__5 = _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__5();
lean_mark_persistent(l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__5);
l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__6 = _init_l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__6();
lean_mark_persistent(l_Lean_Linter_logLint___at___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___spec__6___closed__6);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__4);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__5 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_inductiveSyntaxToView___closed__5);
l_Lean_Elab_Command_elabClassInductive___closed__1 = _init_l_Lean_Elab_Command_elabClassInductive___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabClassInductive___closed__1);
l_Lean_Elab_Command_elabClassInductive___closed__2 = _init_l_Lean_Elab_Command_elabClassInductive___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabClassInductive___closed__2);
l_Lean_Elab_Command_elabClassInductive___closed__3 = _init_l_Lean_Elab_Command_elabClassInductive___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabClassInductive___closed__3);
l_Lean_Elab_Command_expandNamespacedDeclaration___closed__1 = _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandNamespacedDeclaration___closed__1);
l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2 = _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandNamespacedDeclaration___closed__2);
l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3 = _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandNamespacedDeclaration___closed__3);
l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4 = _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandNamespacedDeclaration___closed__4);
l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5 = _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandNamespacedDeclaration___closed__5);
l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6 = _init_l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandNamespacedDeclaration___closed__6);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__1);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__2);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__3);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1___closed__1);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandNamespacedDeclaration_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__1);
l_Lean_Elab_Command_elabDeclaration___closed__2 = _init_l_Lean_Elab_Command_elabDeclaration___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__2);
l_Lean_Elab_Command_elabDeclaration___closed__3 = _init_l_Lean_Elab_Command_elabDeclaration___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__3);
l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabDeclaration__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabDeclaration_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabDeclaration__2(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__1);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__2);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__3);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__4);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__5);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__6);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__7);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__8);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__9);
l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10 = _init_l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Declaration_0__Lean_Elab_Command_isMutualPreambleCommand___closed__10);
l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__1 = _init_l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__1);
l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__2 = _init_l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__2);
l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__3 = _init_l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__3();
lean_mark_persistent(l_panic___at_Lean_Elab_Command_expandMutualNamespace___spec__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandMutualNamespace___spec__3___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__4);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualNamespace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Command_expandMutualElement___closed__1 = _init_l_Lean_Elab_Command_expandMutualElement___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualElement___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualElement__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualElement_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Command_expandMutualPreamble___closed__1 = _init_l_Lean_Elab_Command_expandMutualPreamble___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualPreamble___closed__1);
l_Lean_Elab_Command_expandMutualPreamble___closed__2 = _init_l_Lean_Elab_Command_expandMutualPreamble___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualPreamble___closed__2);
l_Lean_Elab_Command_expandMutualPreamble___closed__3 = _init_l_Lean_Elab_Command_expandMutualPreamble___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandMutualPreamble___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMutualPreamble_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Command_elabMutual___closed__1 = _init_l_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__1);
l_Lean_Elab_Command_elabMutual___closed__2 = _init_l_Lean_Elab_Command_elabMutual___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__2);
l_Lean_Elab_Command_elabMutual___closed__3 = _init_l_Lean_Elab_Command_elabMutual___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__3);
l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMutual__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMutual_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMutual__2(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabAttr___spec__1___closed__6);
l_panic___at_Lean_Elab_Command_elabAttr___spec__3___closed__1 = _init_l_panic___at_Lean_Elab_Command_elabAttr___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Command_elabAttr___spec__3___closed__1);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__1 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__1();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__1);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__2 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__2();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__2);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__3 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__3();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__3);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__4 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__4();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__4);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__5 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__5();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Command_elabAttr___spec__2___closed__5);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__3);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__4 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__4();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAttr___spec__5___closed__4);
l_Lean_Elab_Command_elabAttr___closed__1 = _init_l_Lean_Elab_Command_elabAttr___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAttr___closed__1);
l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabAttr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabAttr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Command_elabInitialize___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__1);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__2);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__3);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__4);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__5);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__6);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__7 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__7);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__8);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__9 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__9);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__10);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__11 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__11);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__12 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__12);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__13);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__14);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__15 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__15);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__16);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__17 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__17);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__18);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__19);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__20 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__20);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__21);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__22 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__22);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__23);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__24);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__25 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__25();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__25);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__26);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__27 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__27();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__27);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__28);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__29);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__30 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__30();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__30);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__31 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__31();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__31);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__32 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__32();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__32);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__33);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__34 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__34();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__34);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__35);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__36);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__37 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__37();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__37);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__38 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__38();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__38);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__39 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__39();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__39);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__40);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__41 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__41();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__41);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__42);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__43);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__44);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__45 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__45();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__45);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__46 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__46();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__46);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__47);
l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48 = _init_l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__1___closed__48);
l_Lean_Elab_Command_elabInitialize___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__2___closed__1);
l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2 = _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__2___closed__2);
l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3 = _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__2___closed__3);
l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4 = _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__2___closed__4);
l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5 = _init_l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__2___closed__5);
l_Lean_Elab_Command_elabInitialize___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__3___closed__1);
l_Lean_Elab_Command_elabInitialize___lambda__3___closed__2 = _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__3___closed__2);
l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3 = _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__3___closed__3);
l_Lean_Elab_Command_elabInitialize___lambda__3___closed__4 = _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__3___closed__4);
l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5 = _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__3___closed__5);
l_Lean_Elab_Command_elabInitialize___lambda__3___closed__6 = _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__3___closed__6);
l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7 = _init_l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__3___closed__7);
l_Lean_Elab_Command_elabInitialize___lambda__6___closed__1 = _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__6___closed__1);
l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2 = _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__6___closed__2);
l_Lean_Elab_Command_elabInitialize___lambda__6___closed__3 = _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__6___closed__3);
l_Lean_Elab_Command_elabInitialize___lambda__6___closed__4 = _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__6___closed__4);
l_Lean_Elab_Command_elabInitialize___lambda__6___closed__5 = _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__6___closed__5);
l_Lean_Elab_Command_elabInitialize___lambda__6___closed__6 = _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__6___closed__6);
l_Lean_Elab_Command_elabInitialize___lambda__6___closed__7 = _init_l_Lean_Elab_Command_elabInitialize___lambda__6___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___lambda__6___closed__7);
l_Lean_Elab_Command_elabInitialize___closed__1 = _init_l_Lean_Elab_Command_elabInitialize___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___closed__1);
l_Lean_Elab_Command_elabInitialize___closed__2 = _init_l_Lean_Elab_Command_elabInitialize___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___closed__2);
l_Lean_Elab_Command_elabInitialize___closed__3 = _init_l_Lean_Elab_Command_elabInitialize___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___closed__3);
l_Lean_Elab_Command_elabInitialize___closed__4 = _init_l_Lean_Elab_Command_elabInitialize___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___closed__4);
l_Lean_Elab_Command_elabInitialize___closed__5 = _init_l_Lean_Elab_Command_elabInitialize___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabInitialize___closed__5);
l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitialize__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabInitialize__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__2 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__2();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__3 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__3();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__3);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__4 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__4();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__4);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__5 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__5();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__5);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__6 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__6();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__6);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__7 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__7();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__7);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__8 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__8();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__8);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__9 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__9();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__9);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__10 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__10();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__10);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__11 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__11();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__11);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__12 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__12();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__12);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__13 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__13();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024____closed__13);
if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Declaration___hyg_9024_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
