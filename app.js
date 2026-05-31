"use strict";

const STORAGE_KEY = "buaa-logic-proof-theorems-v1";

const axiomPatterns = [
  {
    id: "A1",
    label: "公理 1",
    text: "A -> (B -> A)",
    ast: null,
  },
  {
    id: "A2",
    label: "公理 2",
    text: "(A -> (B -> C)) -> ((A -> B) -> (A -> C))",
    ast: null,
  },
  {
    id: "A3",
    label: "公理 3",
    text: "(~B -> ~A) -> (A -> B)",
    ast: null,
  },
];

const demoProof = [
  { formula: "A -> ((A -> A) -> A)", mode: "axiom" },
  { formula: "(A -> ((A -> A) -> A)) -> ((A -> (A -> A)) -> (A -> A))", mode: "axiom" },
  { formula: "(A -> (A -> A)) -> (A -> A)", mode: "mp", premise: 1, implication: 2 },
  { formula: "A -> (A -> A)", mode: "axiom" },
  { formula: "A -> A", mode: "mp", premise: 4, implication: 3 },
];

const state = {
  target: null,
  currentGoal: null,
  deductionStack: [],
  steps: [],
  theorems: [],
  acceptedShown: false,
};

const el = {
  targetInput: document.querySelector("#targetInput"),
  setTargetBtn: document.querySelector("#setTargetBtn"),
  targetStatus: document.querySelector("#targetStatus"),
  targetPreview: document.querySelector("#targetPreview"),
  deductionStack: document.querySelector("#deductionStack"),
  enterDeductionBtn: document.querySelector("#enterDeductionBtn"),
  exitDeductionBtn: document.querySelector("#exitDeductionBtn"),
  formulaInputLabel: document.querySelector("#formulaInputLabel"),
  formulaInput: document.querySelector("#formulaInput"),
  sourceModes: document.querySelectorAll("input[name='sourceMode']"),
  premiseControls: document.querySelector("#premiseControls"),
  premiseSelect: document.querySelector("#premiseSelect"),
  mpControls: document.querySelector("#mpControls"),
  mpPremiseInput: document.querySelector("#mpPremiseInput"),
  mpImplicationInput: document.querySelector("#mpImplicationInput"),
  theoremControls: document.querySelector("#theoremControls"),
  theoremSelect: document.querySelector("#theoremSelect"),
  theoremPremiseControls: document.querySelector("#theoremPremiseControls"),
  addStepBtn: document.querySelector("#addStepBtn"),
  checkCurrentBtn: document.querySelector("#checkCurrentBtn"),
  composerMessage: document.querySelector("#composerMessage"),
  proofBody: document.querySelector("#proofBody"),
  emptyProofTemplate: document.querySelector("#emptyProofTemplate"),
  proofGraph: document.querySelector("#proofGraph"),
  saveTheoremBtn: document.querySelector("#saveTheoremBtn"),
  loadDemoBtn: document.querySelector("#loadDemoBtn"),
  resetProofBtn: document.querySelector("#resetProofBtn"),
  theoremLibrary: document.querySelector("#theoremLibrary"),
  dependencyGraphBtn: document.querySelector("#dependencyGraphBtn"),
  dependencyGraphSection: document.querySelector("#dependencyGraphSection"),
  theoremDependencyGraph: document.querySelector("#theoremDependencyGraph"),
  clearLibraryBtn: document.querySelector("#clearLibraryBtn"),
  acceptedToast: document.querySelector("#acceptedToast"),
};

class Tokenizer {
  constructor(input) {
    this.input = input;
    this.index = 0;
    this.tokens = [];
  }

  scan() {
    while (this.index < this.input.length) {
      const char = this.input[this.index];
      if (/\s/.test(char)) {
        this.index += 1;
        continue;
      }
      if (char === "(" || char === ")" || char === "~" || char === "&" || char === "|") {
        this.tokens.push({ type: char, value: char });
        this.index += 1;
        continue;
      }
      if (char === "-" && this.input[this.index + 1] === ">") {
        this.tokens.push({ type: "->", value: "->" });
        this.index += 2;
        continue;
      }
      if (/[A-Za-z]/.test(char)) {
        let value = char;
        this.index += 1;
        while (this.index < this.input.length && /[A-Za-z0-9_]/.test(this.input[this.index])) {
          value += this.input[this.index];
          this.index += 1;
        }
        this.tokens.push({ type: "var", value });
        continue;
      }
      throw new Error(`无法识别的字符 "${char}"`);
    }
    this.tokens.push({ type: "eof", value: "" });
    return this.tokens;
  }
}

class Parser {
  constructor(input) {
    this.tokens = new Tokenizer(input).scan();
    this.index = 0;
  }

  parse() {
    const expression = this.parseImplication();
    if (!this.match("eof")) {
      throw new Error(`公式在 "${this.current().value}" 附近没有解析完`);
    }
    return expression;
  }

  parseImplication() {
    const left = this.parseOr();
    if (this.match("->")) {
      const right = this.parseImplication();
      return { type: "implies", left, right };
    }
    return left;
  }

  parseOr() {
    let node = this.parseAnd();
    while (this.match("|")) {
      node = { type: "or", left: node, right: this.parseAnd() };
    }
    return node;
  }

  parseAnd() {
    let node = this.parseNot();
    while (this.match("&")) {
      node = { type: "and", left: node, right: this.parseNot() };
    }
    return node;
  }

  parseNot() {
    if (this.match("~")) {
      return { type: "not", value: this.parseNot() };
    }
    return this.parsePrimary();
  }

  parsePrimary() {
    const token = this.current();
    if (this.match("var")) {
      return { type: "var", name: token.value };
    }
    if (this.match("(")) {
      const expression = this.parseImplication();
      this.consume(")", "缺少右括号");
      return expression;
    }
    throw new Error(`需要命题变量或左括号，但遇到 "${token.value || "结尾"}"`);
  }

  current() {
    return this.tokens[this.index];
  }

  match(type) {
    if (this.current().type !== type) {
      return false;
    }
    this.index += 1;
    return true;
  }

  consume(type, message) {
    if (!this.match(type)) {
      throw new Error(message);
    }
  }
}

function normalizeFormulaInput(text) {
  return String(text || "")
    .replaceAll("（", "(")
    .replaceAll("）", ")")
    .replaceAll("→", "->")
    .replaceAll("⇒", "->")
    .replaceAll("¬", "~")
    .replaceAll("～", "~")
    .replaceAll("！", "~")
    .replaceAll("∧", "&")
    .replaceAll("∨", "|")
    .replaceAll("，", ",")
    .replace(/[\s,，。；;]+$/g, "")
    .trim();
}

function parseFormula(text) {
  const trimmed = normalizeFormulaInput(text);
  if (!trimmed) {
    throw new Error("请输入公式");
  }
  return expandConnectives(new Parser(trimmed).parse());
}

function parseFormulaRaw(text) {
  const trimmed = normalizeFormulaInput(text);
  if (!trimmed) {
    throw new Error("请输入公式");
  }
  return new Parser(trimmed).parse();
}

function expandConnectives(node) {
  if (node.type === "var") {
    return cloneAst(node);
  }
  if (node.type === "not") {
    return { type: "not", value: expandConnectives(node.value) };
  }
  if (node.type === "implies") {
    return {
      type: "implies",
      left: expandConnectives(node.left),
      right: expandConnectives(node.right),
    };
  }
  if (node.type === "or") {
    return {
      type: "implies",
      left: { type: "not", value: expandConnectives(node.left) },
      right: expandConnectives(node.right),
    };
  }
  if (node.type === "and") {
    return {
      type: "not",
      value: {
        type: "implies",
        left: expandConnectives(node.left),
        right: { type: "not", value: expandConnectives(node.right) },
      },
    };
  }
  return cloneAst(node);
}

function normalizeFormulaForDisplay(text) {
  const raw = parseFormulaRaw(text);
  const expanded = expandConnectives(raw);
  return {
    raw,
    expanded,
    rawFormula: formatFormula(raw),
    expandedFormula: formatFormula(expanded),
    changed: !astEquals(raw, expanded),
  };
}

function splitTopLevel(text, separator) {
  const parts = [];
  let depth = 0;
  let start = 0;
  for (let index = 0; index < text.length; index += 1) {
    const char = text[index];
    if (char === "(") depth += 1;
    if (char === ")") depth -= 1;
    if (char === separator && depth === 0) {
      parts.push(text.slice(start, index).trim());
      start = index + 1;
    }
  }
  parts.push(text.slice(start).trim());
  return parts.filter(Boolean);
}

function parseTarget(text) {
  const normalized = normalizeFormulaInput(text);
  const sequentIndex = normalized.indexOf("=>");
  let ast = null;
  let sequentPremises = [];
  let formula = "";
  let conclusionFormula = "";
  if (sequentIndex === -1) {
    ast = parseFormula(normalized);
    formula = formatFormula(ast);
    conclusionFormula = formula;
  } else {
    const premiseText = normalized.slice(0, sequentIndex).trim();
    const conclusionText = normalized.slice(sequentIndex + 2).trim();
    if (!conclusionText) {
      throw new Error("前提集合后需要写出结论");
    }
    sequentPremises = splitTopLevel(premiseText, ",").map((part) => {
      const premiseAst = parseFormula(part);
      return { ast: premiseAst, formula: formatFormula(premiseAst) };
    });
    ast = parseFormula(conclusionText);
    conclusionFormula = formatFormula(ast);
    formula = sequentPremises.length ? `${sequentPremises.map((item) => item.formula).join(", ")} => ${conclusionFormula}` : conclusionFormula;
  }
  return {
    ast,
    assumptions: sequentPremises,
    premises: sequentPremises,
    formula,
    conclusionAst: cloneAst(ast),
    conclusionFormula,
    sequentMode: sequentIndex !== -1,
  };
}

function precedence(node) {
  if (node.type === "implies") return 1;
  if (node.type === "or") return 2;
  if (node.type === "and") return 3;
  if (node.type === "not") return 4;
  return 5;
}

function formatFormula(node, parentPrecedence = 0, side = "") {
  let text = "";
  if (node.type === "var") {
    text = node.name;
  } else if (node.type === "not") {
    const inner = formatFormula(node.value, precedence(node), "right");
    text = `~${inner}`;
  } else {
    const op = node.type === "implies" ? "->" : node.type === "and" ? "&" : "|";
    const own = precedence(node);
    const left = formatFormula(node.left, own, "left");
    const right = formatFormula(node.right, own, "right");
    text = `${left} ${op} ${right}`;
  }
  const needParens =
    precedence(node) < parentPrecedence ||
    (node.type === "implies" && precedence(node) === parentPrecedence);
  return needParens ? `(${text})` : text;
}

function astEquals(a, b) {
  if (!a || !b || a.type !== b.type) return false;
  if (a.type === "var") return a.name === b.name;
  if (a.type === "not") return astEquals(a.value, b.value);
  return astEquals(a.left, b.left) && astEquals(a.right, b.right);
}

function instantiatePattern(node, bindings) {
  if (isPatternVariable(node) && bindings.has(node.name)) {
    return cloneAst(bindings.get(node.name));
  }
  if (node.type === "var") {
    return cloneAst(node);
  }
  if (node.type === "not") {
    return { type: "not", value: instantiatePattern(node.value, bindings) };
  }
  return {
    type: node.type,
    left: instantiatePattern(node.left, bindings),
    right: instantiatePattern(node.right, bindings),
  };
}

function impliesAst(left, right) {
  return {
    type: "implies",
    left: cloneAst(left),
    right: cloneAst(right),
  };
}

function nestedImplication(premises, conclusion) {
  return premises.reduceRight((right, premise) => impliesAst(premise.ast || premise, right), cloneAst(conclusion));
}

function makeProofLine(ast, mode, detail, refs = []) {
  return {
    ast: cloneAst(ast),
    formula: formatFormula(ast),
    mode,
    detail,
    refs,
  };
}

function cloneAst(node) {
  return JSON.parse(JSON.stringify(node));
}

function isPatternVariable(node) {
  return node.type === "var" && /^[A-Z]$/.test(node.name);
}

function matchPattern(pattern, actual, bindings = new Map()) {
  if (isPatternVariable(pattern)) {
    const existing = bindings.get(pattern.name);
    if (!existing) {
      bindings.set(pattern.name, actual);
      return true;
    }
    return astEquals(existing, actual);
  }
  if (pattern.type !== actual.type) {
    return false;
  }
  if (pattern.type === "var") {
    return pattern.name === actual.name;
  }
  if (pattern.type === "not") {
    return matchPattern(pattern.value, actual.value, bindings);
  }
  return matchPattern(pattern.left, actual.left, bindings) && matchPattern(pattern.right, actual.right, bindings);
}

function findAxiomMatch(ast) {
  for (const axiom of axiomPatterns) {
    const bindings = new Map();
    if (matchPattern(axiom.ast, ast, bindings)) {
      const substitution = [...bindings.entries()]
        .map(([name, value]) => `${name}=${formatFormula(value)}`)
        .join(", ");
      return {
        ok: true,
        axiom,
        detail: substitution ? `${axiom.label}，代换：${substitution}` : axiom.label,
      };
    }
  }
  return {
    ok: false,
    detail: "不是三条公理中任意一条的合法实例",
  };
}

function stepAt(number) {
  if (!Number.isInteger(number) || number < 1 || number > state.steps.length) {
    return null;
  }
  return state.steps[number - 1];
}

function checkMp(ast, premiseNumber, implicationNumber) {
  const derived = deriveMp(premiseNumber, implicationNumber);
  if (!derived.ok) {
    return derived;
  }
  if (!astEquals(derived.ast, ast)) {
    return {
      ok: false,
      detail: `MP 应推出 ${derived.formula}，而不是 ${formatFormula(ast)}`,
    };
  }
  return derived;
}

function deriveMp(premiseNumber, implicationNumber) {
  const premise = stepAt(premiseNumber);
  const implication = stepAt(implicationNumber);
  if (!premise || !implication) {
    return { ok: false, detail: "MP 需要填写已经存在的两个步骤号" };
  }

  const direct = deriveMpOrdered(premise, implication, premiseNumber, implicationNumber);
  if (direct.ok) {
    return direct;
  }

  const swapped = deriveMpOrdered(implication, premise, implicationNumber, premiseNumber);
  if (swapped.ok) {
    return {
      ...swapped,
      detail: `已自动识别两个步骤的角色：${swapped.detail}`,
    };
  }

  return direct;
}

function deriveMpOrdered(premise, implication, premiseNumber, implicationNumber) {
  if (implication.ast.type !== "implies") {
    return { ok: false, detail: `步骤 ${implicationNumber} 不是蕴含式 P -> Q` };
  }
  if (!astEquals(implication.ast.left, premise.ast)) {
    return {
      ok: false,
      detail: `步骤 ${implicationNumber} 的前件是 ${formatFormula(implication.ast.left)}，与步骤 ${premiseNumber} 不一致`,
    };
  }
  return {
    ok: true,
    ast: cloneAst(implication.ast.right),
    formula: formatFormula(implication.ast.right),
    detail: `由步骤 ${premiseNumber} 和步骤 ${implicationNumber} 使用 MP 得到`,
    refs: [premiseNumber, implicationNumber],
  };
}

function checkTheorem(ast, theoremId) {
  const derived = deriveTheorem(theoremId);
  if (!derived.ok) {
    return derived;
  }
  if (!astEquals(derived.ast, ast)) {
    return { ok: false, detail: `所选定理应推出 ${derived.formula}，与当前公式不一致` };
  }
  return derived;
}

function deriveTheorem(theoremId) {
  const theorem = state.theorems.find((item) => item.id === theoremId);
  if (!theorem) {
    return { ok: false, detail: "请先在定理库中选择一个定理" };
  }

  const premises = theorem.premises || [];
  if (!premises.length) {
    return {
      ok: true,
      ast: cloneAst(theorem.ast),
      formula: formatFormula(theorem.ast),
      detail: `调用已证定理：${theorem.title || theorem.formula || formatFormula(theorem.ast)}`,
      theoremId,
      refs: [],
    };
  }

  const inputs = [...el.theoremPremiseControls.querySelectorAll(".theorem-premise-step")];
  if (inputs.length !== premises.length) {
    return { ok: false, detail: "这个定理需要先填写所有前提对应的步骤号" };
  }

  const bindings = new Map();
  const refs = [];
  for (let index = 0; index < premises.length; index += 1) {
    const stepNumber = Number.parseInt(inputs[index].value, 10);
    const step = stepAt(stepNumber);
    if (!step) {
      return { ok: false, detail: `前提 ${index + 1} 需要填写已经存在的步骤号` };
    }
    if (!matchPattern(premises[index].ast, step.ast, bindings)) {
      return {
        ok: false,
        detail: `步骤 ${stepNumber} 不能匹配前提 ${index + 1}：${premises[index].formula}`,
      };
    }
    refs.push(stepNumber);
  }

  const ast = instantiatePattern(theorem.ast, bindings);
  const formula = formatFormula(ast);
  return {
    ok: true,
    ast,
    formula,
    detail: `由定理 ${theorem.formula} 和步骤 ${refs.join(", ")} 得到`,
    theoremId,
    refs,
  };
}

function instantiateTheoremConclusion(theorem, requestedAst) {
  const bindings = new Map();
  if (!matchPattern(theorem.ast, requestedAst, bindings)) {
    return {
      ok: false,
      detail: `所选定理 ${theorem.formula} 不能实例化为 ${formatFormula(requestedAst)}`,
    };
  }
  const substitution = [...bindings.entries()]
    .map(([name, value]) => `${name}=${formatFormula(value)}`)
    .join(", ");
  return {
    ok: true,
    ast: cloneAst(requestedAst),
    formula: formatFormula(requestedAst),
    detail: substitution ? `调用已证定理：${theorem.formula}，代换：${substitution}` : `调用已证定理：${theorem.formula}`,
    theoremId: theorem.id,
    refs: [],
  };
}

function appendLine(proof, ast, mode, detail, refs = []) {
  proof.push(makeProofLine(ast, mode, detail, refs));
  return proof.length;
}

function appendSelfImplicationProof(proof, assumptionAst) {
  const a = cloneAst(assumptionAst);
  const aImpA = impliesAst(a, a);
  const line1Ast = impliesAst(a, impliesAst(aImpA, a));
  const line1 = appendLine(proof, line1Ast, "axiom", "演绎转换：公理 1");
  const line2Ast = impliesAst(line1Ast, impliesAst(impliesAst(a, aImpA), aImpA));
  const line2 = appendLine(proof, line2Ast, "axiom", "演绎转换：公理 2");
  const line3 = appendLine(proof, impliesAst(impliesAst(a, aImpA), aImpA), "mp", `MP ${line1}, ${line2}`, [line1, line2]);
  const line4 = appendLine(proof, impliesAst(a, aImpA), "axiom", "演绎转换：公理 1");
  return appendLine(proof, aImpA, "mp", `MP ${line4}, ${line3}`, [line4, line3]);
}

function appendBaseToImplication(proof, baseAst, assumptionAst, detail, mode = "theorem") {
  const base = appendLine(proof, baseAst, mode, detail);
  const lift = appendLine(proof, impliesAst(baseAst, impliesAst(assumptionAst, baseAst)), "axiom", "演绎转换：公理 1");
  const result = appendLine(proof, impliesAst(assumptionAst, baseAst), "mp", `MP ${base}, ${lift}`, [base, lift]);
  return result;
}

function appendMpImplication(proof, assumptionAst, antecedentAst, consequentAst, mappedAntecedent, mappedImplication) {
  const axiom2Ast = impliesAst(
    impliesAst(assumptionAst, impliesAst(antecedentAst, consequentAst)),
    impliesAst(impliesAst(assumptionAst, antecedentAst), impliesAst(assumptionAst, consequentAst)),
  );
  const axiom = appendLine(proof, axiom2Ast, "axiom", "演绎转换：公理 2");
  const middle = appendLine(proof, impliesAst(impliesAst(assumptionAst, antecedentAst), impliesAst(assumptionAst, consequentAst)), "mp", `MP ${mappedImplication}, ${axiom}`, [
    mappedImplication,
    axiom,
  ]);
  return appendLine(proof, impliesAst(assumptionAst, consequentAst), "mp", `MP ${mappedAntecedent}, ${middle}`, [mappedAntecedent, middle]);
}

function removeAssumptionWithDeduction(sourceSteps, assumptionAst) {
  const proof = [];
  const lineMap = new Map();

  sourceSteps.forEach((step, index) => {
    const originalNumber = index + 1;
    if (astEquals(step.ast, assumptionAst)) {
      lineMap.set(originalNumber, appendSelfImplicationProof(proof, assumptionAst));
      return;
    }

    if (step.mode === "mp" && step.refs && step.refs.length === 2) {
      const refA = sourceSteps[step.refs[0] - 1];
      const refB = sourceSteps[step.refs[1] - 1];
      let antecedentStep = refA;
      let implicationStep = refB;
      let antecedentOriginal = step.refs[0];
      let implicationOriginal = step.refs[1];
      if (!implicationStep || implicationStep.ast.type !== "implies" || !antecedentStep || !astEquals(implicationStep.ast.left, antecedentStep.ast)) {
        antecedentStep = refB;
        implicationStep = refA;
        antecedentOriginal = step.refs[1];
        implicationOriginal = step.refs[0];
      }
      if (
        implicationStep &&
        antecedentStep &&
        implicationStep.ast.type === "implies" &&
        astEquals(implicationStep.ast.left, antecedentStep.ast) &&
        astEquals(implicationStep.ast.right, step.ast)
      ) {
        const mappedAntecedent = lineMap.get(antecedentOriginal);
        const mappedImplication = lineMap.get(implicationOriginal);
        lineMap.set(originalNumber, appendMpImplication(proof, assumptionAst, antecedentStep.ast, step.ast, mappedAntecedent, mappedImplication));
        return;
      }
    }

    const detail =
      step.mode === "premise"
        ? `保留未消去前提：${step.formula}`
        : step.mode === "axiom"
          ? `保留公理实例：${step.formula}`
          : step.mode === "theorem"
            ? `保留定理调用：${step.detail}`
            : `保留原步骤：${step.detail}`;
    const baseMode = step.mode === "premise" || step.mode === "axiom" || step.mode === "theorem" ? step.mode : "theorem";
    lineMap.set(originalNumber, appendBaseToImplication(proof, step.ast, assumptionAst, detail, baseMode));
  });

  return proof;
}

function enterDeductionLayer() {
  if (!state.currentGoal) {
    setMessage("请先设置目标定理", "bad");
    return;
  }
  if (state.currentGoal.ast.type !== "implies") {
    setMessage("当前子目标不是蕴含式，不能继续进入演绎子证明", "bad");
    return;
  }
  state.deductionStack.push({
    ast: cloneAst(state.currentGoal.ast.left),
    formula: formatFormula(state.currentGoal.ast.left),
  });
  state.currentGoal = {
    ast: cloneAst(state.currentGoal.ast.right),
    formula: formatFormula(state.currentGoal.ast.right),
  };
  clearProofForDeductionChange(`已进入一层演绎，当前子目标：${state.currentGoal.formula}`);
}

function exitDeductionLayer() {
  const fixedCount = getFixedPremiseCount();
  if (state.deductionStack.length <= fixedCount) {
    setMessage("当前没有可撤销的演绎假设", "bad");
    return;
  }
  state.deductionStack.pop();
  state.currentGoal = computeGoalFromStack();
  clearProofForDeductionChange(`已撤销一层演绎，当前子目标：${state.currentGoal.formula}`);
}

function clearProofForDeductionChange(message) {
  state.steps = [];
  state.acceptedShown = false;
  updateTargetPreview();
  setMessage(`${message}。证明步骤已清空。`, "good");
  render();
}

function updateTargetPreview() {
  if (!state.target || !state.currentGoal) {
    el.targetPreview.textContent = "";
    return;
  }
  const assumptions = getTargetAssumptions();
  const prefix = assumptions.length ? `${assumptions.map((item) => item.formula).join(", ")} ⊢ ` : "";
  el.targetPreview.textContent = `原始目标：${state.target.formula}；当前子目标：${prefix}${state.currentGoal.formula}`;
}

function computeGoalFromStack() {
  let cursor = state.target ? cloneAst(state.target.sequentMode ? state.target.ast : state.target.ast) : null;
  const fixedCount = getFixedPremiseCount();
  for (let index = fixedCount; index < state.deductionStack.length; index += 1) {
    if (!cursor || cursor.type !== "implies") break;
    cursor = cursor.right;
  }
  return {
    ast: cursor,
    formula: cursor ? formatFormula(cursor) : "",
  };
}

function getSelectedMode() {
  const checked = [...el.sourceModes].find((item) => item.checked);
  return checked ? checked.value : "axiom";
}

function readCurrentCandidate() {
  const mode = getSelectedMode();
  if (mode === "mp") {
    const premise = Number.parseInt(el.mpPremiseInput.value, 10);
    const implication = Number.parseInt(el.mpImplicationInput.value, 10);
    return { mode, ...deriveMp(premise, implication) };
  }
  if (mode === "premise") {
    const index = Number.parseInt(el.premiseSelect.value, 10);
    const premise = getTargetAssumptions()[index];
    if (!premise) {
      return { ok: false, detail: "当前目标没有可用的临时假设" };
    }
    return {
      ok: true,
      ast: cloneAst(premise.ast),
      formula: premise.formula,
      mode,
      detail: `临时假设 ${index + 1}`,
      refs: [],
    };
  }
  if (mode === "theorem") {
    const theorem = state.theorems.find((item) => item.id === el.theoremSelect.value);
    if (!theorem) {
      return { ok: false, detail: "请先在定理库中选择一个定理" };
    }
    if ((theorem.premises || []).length) {
      return { mode, ...deriveTheorem(el.theoremSelect.value) };
    }
    const expansion = normalizeFormulaForDisplay(el.formulaInput.value);
    return { mode, expansion, ...instantiateTheoremConclusion(theorem, expansion.expanded) };
  }
  const expansion = normalizeFormulaForDisplay(el.formulaInput.value);
  const ast = expansion.expanded;
  if (mode === "axiom") {
    const axiomResult = findAxiomMatch(ast);
    return { ast, formula: formatFormula(ast), mode, expansion, ...axiomResult };
  }
  return { ok: false, detail: "未知的步骤来源" };
}

function addStep() {
  try {
    const result = readCurrentCandidate();
    if (!result.ok) {
      setMessage(result.detail, "bad");
      return;
    }
    state.steps.push({
      id: crypto.randomUUID(),
      ast: result.ast,
      formula: result.formula,
      mode: result.mode,
      detail: result.detail,
      refs: result.refs || [],
      theoremId: result.theoremId || null,
      axiomId: result.axiom ? result.axiom.id : null,
    });
    el.formulaInput.value = "";
    el.mpPremiseInput.value = "";
    el.mpImplicationInput.value = "";
    setMessage(`步骤 ${state.steps.length} 已添加：${result.detail}`, "good");
    render();
  } catch (error) {
    setMessage(error.message, "bad");
  }
}

function checkCurrentInput() {
  try {
    const result = readCurrentCandidate();
    const mode = getSelectedMode();
    const prefix =
      mode === "mp" || mode === "theorem"
        ? `可推出：${result.formula}。`
        : mode === "premise"
          ? `可添加临时假设：${result.formula}。`
          : "合法：";
    const expansion = result.expansion && result.expansion.changed ? ` 已按定义展开：${result.expansion.rawFormula} = ${result.expansion.expandedFormula}。` : "";
    setMessage(result.ok ? `${prefix}${result.detail}${expansion}` : result.detail, result.ok ? "good" : "bad");
  } catch (error) {
    setMessage(error.message, "bad");
  }
}

function setMessage(text, kind = "") {
  el.composerMessage.textContent = text;
  el.composerMessage.className = `message-line ${kind}`.trim();
}

function setTarget() {
  try {
    const expansion = normalizeTargetForDisplay(el.targetInput.value);
    state.target = parseTarget(el.targetInput.value);
    state.target.rawFormula = expansion.rawFormula;
    state.target.expandedFormula = expansion.expandedFormula;
    state.target.expandedFromSugar = expansion.changed;
    state.currentGoal = {
      ast: cloneAst(state.target.ast),
      formula: state.target.formula,
    };
    state.deductionStack = state.target.sequentMode
      ? state.target.premises.map((premise) => ({ ast: cloneAst(premise.ast), formula: premise.formula }))
      : [];
    state.steps = [];
    state.acceptedShown = false;
    updateTargetPreview();
    const expansionMessage = state.target.expandedFromSugar ? `；已按定义展开：${state.target.rawFormula} = ${state.target.expandedFormula}` : "";
    setMessage(`目标已设为：${state.target.formula}${expansionMessage}`, "good");
    render();
  } catch (error) {
    el.targetPreview.textContent = error.message;
    el.targetStatus.textContent = "有错误";
    el.targetStatus.className = "status-pill warning";
  }
}

function normalizeTargetForDisplay(text) {
  const normalized = normalizeFormulaInput(text);
  const sequentIndex = normalized.indexOf("=>");
  if (sequentIndex === -1) {
    return normalizeFormulaForDisplay(normalized);
  }
  const premiseText = normalized.slice(0, sequentIndex).trim();
  const conclusionText = normalized.slice(sequentIndex + 2).trim();
  const rawPremises = splitTopLevel(premiseText, ",").map((part) => parseFormulaRaw(part));
  const expandedPremises = rawPremises.map(expandConnectives);
  const rawConclusion = parseFormulaRaw(conclusionText);
  const expandedConclusion = expandConnectives(rawConclusion);
  const rawFormula = `${rawPremises.map(formatFormula).join(", ")} => ${formatFormula(rawConclusion)}`;
  const expandedFormula = `${expandedPremises.map(formatFormula).join(", ")} => ${formatFormula(expandedConclusion)}`;
  return {
    rawFormula,
    expandedFormula,
    changed: rawFormula !== expandedFormula,
  };
}

function isGoalProved() {
  if (!state.target) return false;
  return state.steps.some((step) => astEquals(step.ast, state.currentGoal.ast));
}

function saveCurrentTheorem() {
  if (!state.target || !isGoalProved()) {
    return;
  }
  const theoremPremises = state.target.sequentMode ? state.target.premises || [] : [];
  const exists = state.theorems.some((item) => astEquals(item.ast, state.target.ast) && premiseListsEqual(item.premises || [], theoremPremises));
  if (exists) {
    setMessage("定理库里已经有这个定理了", "bad");
    return;
  }
  state.theorems.push({
    id: crypto.randomUUID(),
    ast: cloneAst(state.target.ast),
    premises: theoremPremises.map((premise) => ({
      ast: cloneAst(premise.ast),
      formula: premise.formula,
    })),
    formula: state.target.formula,
    conclusionFormula: state.target.conclusionFormula,
    title: state.target.formula,
    proofSteps: snapshotProofSteps(),
    dependencies: collectProofDependencies(state.steps),
    proofLength: state.steps.length,
    createdAt: new Date().toISOString(),
  });
  persistTheorems();
  setMessage(`已保存定理：${state.target.formula}`, "good");
  render();
}

function snapshotProofSteps() {
  return state.steps.map((step, index) => ({
    number: index + 1,
    ast: cloneAst(step.ast),
    formula: step.formula,
    mode: step.mode,
    detail: step.detail,
    refs: [...(step.refs || [])],
    theoremId: step.theoremId || null,
    axiomId: step.axiomId || null,
  }));
}

function collectProofDependencies(steps) {
  return [...new Set(steps.map((step) => step.theoremId).filter(Boolean))];
}

function premiseListsEqual(a, b) {
  if (a.length !== b.length) return false;
  return a.every((premise, index) => astEquals(premise.ast, b[index].ast));
}

function getTargetAssumptions() {
  return state.deductionStack || [];
}

function getFixedPremiseCount() {
  return state.target && state.target.sequentMode ? (state.target.premises || []).length : 0;
}

function persistTheorems() {
  const payload = state.theorems.map((item) => ({
    id: item.id,
    ast: item.ast,
    premises: item.premises || [],
    formula: item.formula,
    conclusionFormula: item.conclusionFormula || formatFormula(item.ast),
    title: item.title,
    proofLength: item.proofLength,
    proofSteps: item.proofSteps || [],
    dependencies: item.dependencies || collectProofDependencies(item.proofSteps || []),
    createdAt: item.createdAt,
  }));
  localStorage.setItem(STORAGE_KEY, JSON.stringify(payload));
}

function loadTheorems() {
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (!raw) {
      state.theorems = [];
      return;
    }
    state.theorems = JSON.parse(raw).map((item) => ({
      ...item,
      ast: item.ast,
      premises: (item.premises || []).map((premise) => ({
        ast: premise.ast,
        formula: premise.formula || formatFormula(premise.ast),
      })),
      conclusionFormula: item.conclusionFormula || formatFormula(item.ast),
      proofSteps: item.proofSteps || [],
      dependencies: item.dependencies || collectProofDependencies(item.proofSteps || []),
      formula:
        item.formula ||
        ((item.premises || []).length
          ? `${item.premises.map((premise) => premise.formula || formatFormula(premise.ast)).join(", ")} => ${formatFormula(item.ast)}`
          : formatFormula(item.ast)),
    }));
  } catch {
    state.theorems = [];
  }
}

function clearLibrary() {
  if (!state.theorems.length) return;
  const ok = window.confirm("确定要清空定理库吗？这不会影响当前证明步骤。");
  if (!ok) return;
  state.theorems = [];
  persistTheorems();
  render();
}

function resetProof() {
  state.steps = [];
  state.acceptedShown = false;
  setMessage("证明区已清空", "good");
  render();
}

function loadDemo() {
  state.steps = [];
  state.deductionStack = [];
  state.acceptedShown = false;
  el.targetInput.value = "A -> A";
  setTarget();
  for (const item of demoProof) {
    el.formulaInput.value = item.formula;
    if (item.mode === "mp") {
      selectMode("mp");
      el.mpPremiseInput.value = String(item.premise);
      el.mpImplicationInput.value = String(item.implication);
    } else {
      selectMode("axiom");
    }
    const result = readCurrentCandidate();
    if (result.ok) {
      state.steps.push({
        id: crypto.randomUUID(),
        ast: result.ast,
        formula: result.formula,
        mode: result.mode,
        detail: result.detail,
        refs: result.refs || [],
        theoremId: null,
        axiomId: result.axiom ? result.axiom.id : null,
      });
    }
  }
  el.formulaInput.value = "";
  el.mpPremiseInput.value = "";
  el.mpImplicationInput.value = "";
  selectMode("axiom");
  setMessage("已载入 A -> A 的五步证明", "good");
  render();
}

function selectMode(mode) {
  el.sourceModes.forEach((item) => {
    item.checked = item.value === mode;
  });
  updateModeControls();
}

function updateModeControls() {
  const mode = getSelectedMode();
  el.premiseControls.classList.toggle("is-hidden", mode !== "premise");
  el.mpControls.classList.toggle("is-hidden", mode !== "mp");
  el.theoremControls.classList.toggle("is-hidden", mode !== "theorem");
  const autoMode = mode === "mp" || mode === "premise" || mode === "theorem";
  el.formulaInput.disabled = autoMode;
  el.formulaInputLabel.textContent =
    mode === "mp" ? "MP 自动推出的公式" : mode === "premise" ? "选中假设的公式" : mode === "theorem" ? "定理自动推出的公式" : "新步骤公式";
  el.formulaInput.placeholder =
    mode === "mp"
      ? "选择两个步骤后，系统会自动推出结论"
      : mode === "premise"
        ? "选择临时假设后自动填入"
        : mode === "theorem"
          ? "选择定理并填写前提步骤后自动推出"
          : "例如：A -> (B -> A)";
  el.addStepBtn.textContent = mode === "mp" ? "应用 MP" : mode === "theorem" ? "调用定理" : "添加步骤";
  el.checkCurrentBtn.textContent = mode === "mp" ? "预览 MP 结论" : mode === "theorem" ? "预览定理结论" : "检查当前输入";
  if (autoMode) {
    el.formulaInput.value = "";
  }
  if (mode === "premise") {
    renderPremiseOptions();
    const index = Number.parseInt(el.premiseSelect.value, 10);
    const premise = getTargetAssumptions()[index];
    if (premise) el.formulaInput.value = premise.formula;
  }
  if (mode === "theorem") {
    renderTheoremPremiseControls();
    const theorem = state.theorems.find((item) => item.id === el.theoremSelect.value) || state.theorems[0];
    if (theorem) {
      el.formulaInput.disabled = (theorem.premises || []).length > 0;
      el.formulaInput.value = (theorem.premises || []).length ? theorem.conclusionFormula || formatFormula(theorem.ast) : theorem.formula;
    }
  }
}

function renderPremiseOptions() {
  el.premiseSelect.innerHTML = "";
  const premises = getTargetAssumptions();
  if (!premises.length) {
    el.premiseSelect.innerHTML = `<option value="">当前目标没有可拆出的临时假设</option>`;
    return;
  }
  premises.forEach((premise, index) => {
    const option = document.createElement("option");
    option.value = String(index);
    option.textContent = `${index + 1}. ${premise.formula}`;
    el.premiseSelect.appendChild(option);
  });
}

function renderDeductionStack() {
  el.deductionStack.innerHTML = "";
  if (!state.target) {
    el.deductionStack.innerHTML = `<div class="empty-state">先设置一个目标定理。</div>`;
    return;
  }
  if (!state.deductionStack.length) {
    const empty = document.createElement("div");
    empty.className = "stack-item";
    empty.innerHTML = `<span>当前子目标</span><code>${escapeHtml(state.currentGoal.formula)}</code>`;
    el.deductionStack.appendChild(empty);
    return;
  }
  state.deductionStack.forEach((item, index) => {
    const node = document.createElement("div");
    node.className = "stack-item";
    const label = index < getFixedPremiseCount() ? `目标前提 ${index + 1}` : `演绎假设 ${index - getFixedPremiseCount() + 1}`;
    node.innerHTML = `<span>${label}</span><code>${escapeHtml(item.formula)}</code>`;
    el.deductionStack.appendChild(node);
  });
  const goal = document.createElement("div");
  goal.className = "stack-item current-goal";
  goal.innerHTML = `<span>当前子目标</span><code>${escapeHtml(state.currentGoal.formula)}</code>`;
  el.deductionStack.appendChild(goal);
}

function renderTheoremPremiseControls() {
  el.theoremPremiseControls.innerHTML = "";
  const theorem = state.theorems.find((item) => item.id === el.theoremSelect.value);
  if (!theorem || !(theorem.premises || []).length) {
    return;
  }
  theorem.premises.forEach((premise, index) => {
    const label = document.createElement("label");
    label.textContent = `前提 ${index + 1}：${premise.formula}`;
    const input = document.createElement("input");
    input.className = "theorem-premise-step";
    input.type = "number";
    input.min = "1";
    input.placeholder = "对应步骤号";
    label.appendChild(input);
    el.theoremPremiseControls.appendChild(label);
  });
}

function removeStep(index) {
  state.steps.splice(index, 1);
  state.acceptedShown = false;
  state.steps.forEach((step) => {
    step.refs = step.refs.filter((ref) => ref !== index + 1).map((ref) => (ref > index + 1 ? ref - 1 : ref));
    if (step.mode === "mp" && step.refs.length !== 2) {
      step.detail = "依赖步骤被删除，请重新检查该 MP 步骤";
    }
  });
  render();
}

function renderProofTable() {
  el.proofBody.innerHTML = "";
  if (!state.steps.length) {
    el.proofBody.appendChild(el.emptyProofTemplate.content.cloneNode(true));
    return;
  }
  state.steps.forEach((step, index) => {
    const row = document.createElement("tr");
    const sourceText = getSourceText(step.mode);
    row.innerHTML = `
      <td><span class="proof-index">${index + 1}</span></td>
      <td><div class="formula-text">${escapeHtml(step.formula)}</div></td>
      <td><span class="source-badge ${step.mode}">${sourceText}</span></td>
      <td>${escapeHtml(step.detail)}</td>
      <td><button class="delete-step" title="删除步骤" aria-label="删除步骤 ${index + 1}">×</button></td>
    `;
    row.querySelector("button").addEventListener("click", () => removeStep(index));
    el.proofBody.appendChild(row);
  });
}

function getSourceText(mode) {
  if (mode === "axiom") return "公理";
  if (mode === "premise") return "假设";
  if (mode === "mp") return "MP";
  if (mode === "theorem") return "定理";
  return "步骤";
}

function renderGraph() {
  el.proofGraph.innerHTML = "";
  const stage = document.createElement("div");
  stage.className = "graph-stage";
  const width = Math.max(720, state.steps.length * 220 + 80);
  const rows = Math.max(1, Math.ceil(state.steps.length / 3));
  const height = Math.max(300, rows * 140 + 40);
  stage.style.width = `${width}px`;
  stage.style.height = `${height}px`;

  const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg.classList.add("graph-edges");
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  svg.innerHTML = `
    <defs>
      <marker id="arrow" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto" markerUnits="strokeWidth">
        <path d="M0,0 L0,6 L9,3 z" fill="#7a8b87"></path>
      </marker>
    </defs>
  `;
  stage.appendChild(svg);

  if (!state.steps.length) {
    const empty = document.createElement("div");
    empty.className = "empty-state";
    empty.textContent = "添加步骤后，这里会出现证明依赖图。";
    stage.appendChild(empty);
    el.proofGraph.appendChild(stage);
    return;
  }

  const positions = state.steps.map((_, index) => {
    const col = index % 3;
    const row = Math.floor(index / 3);
    return {
      x: 36 + col * 220 + row * 24,
      y: 34 + row * 138,
    };
  });

  state.steps.forEach((step, index) => {
    for (const ref of step.refs) {
      const from = positions[ref - 1];
      const to = positions[index];
      if (!from || !to) continue;
      const line = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const startX = from.x + 180;
      const startY = from.y + 41;
      const endX = to.x;
      const endY = to.y + 41;
      const midX = (startX + endX) / 2;
      line.setAttribute("d", `M ${startX} ${startY} C ${midX} ${startY}, ${midX} ${endY}, ${endX} ${endY}`);
      line.setAttribute("fill", "none");
      line.setAttribute("stroke", "#7a8b87");
      line.setAttribute("stroke-width", "2");
      line.setAttribute("marker-end", "url(#arrow)");
      svg.appendChild(line);
    }
  });

  state.steps.forEach((step, index) => {
    const position = positions[index];
    const node = document.createElement("div");
    const goal = state.target && astEquals(step.ast, state.target.ast);
    node.className = `graph-node ${goal ? "is-goal" : ""}`;
    node.style.left = `${position.x}px`;
    node.style.top = `${position.y}px`;
    node.innerHTML = `
      <small>#${index + 1} · ${getSourceText(step.mode)}</small>
      <strong>${escapeHtml(step.formula)}</strong>
      <span>${escapeHtml(step.refs.length ? `依赖 ${step.refs.join(", ")}` : "基础节点")}</span>
    `;
    stage.appendChild(node);
  });

  el.proofGraph.appendChild(stage);
}

function renderLibrary() {
  el.theoremLibrary.innerHTML = "";
  el.theoremSelect.innerHTML = "";
  if (!state.theorems.length) {
    el.theoremLibrary.innerHTML = `<div class="empty-state">证明目标完成后，可以把它保存为后续可调用定理。</div>`;
    el.theoremSelect.innerHTML = `<option value="">暂无可调用定理</option>`;
    return;
  }
  state.theorems.forEach((theorem, index) => {
    const option = document.createElement("option");
    option.value = theorem.id;
    option.textContent = theorem.formula;
    el.theoremSelect.appendChild(option);

    const item = document.createElement("div");
    item.className = "library-item";
    const proofSteps = theorem.proofSteps || [];
    const dependencies = theorem.dependencies || [];
    item.innerHTML = `
      <div class="library-item-head">
        <button type="button" class="library-pick">
          <div class="library-meta"><span>定理 ${index + 1}</span><span>${proofSteps.length || theorem.proofLength || 1} 步证明 · 依赖 ${dependencies.length}</span></div>
          <code>${escapeHtml(theorem.formula)}</code>
        </button>
        <button type="button" class="delete-theorem" title="删除定理 ${index + 1}" aria-label="删除定理 ${index + 1}">×</button>
      </div>
      <details class="proof-snapshot">
        <summary>保存的证明步骤</summary>
        <ol>
          ${proofSteps.length ? proofSteps.map((step) => `<li><code>${escapeHtml(step.formula)}</code><span>${escapeHtml(getSourceText(step.mode))} · ${escapeHtml(step.detail || "")}</span></li>`).join("") : "<li>旧版本保存的定理没有步骤快照。</li>"}
        </ol>
      </details>
    `;
    item.querySelector(".library-pick").addEventListener("click", () => {
      el.theoremSelect.value = theorem.id;
      selectMode("theorem");
      el.theoremSelect.value = theorem.id;
      renderTheoremPremiseControls();
      el.formulaInput.value = (theorem.premises || []).length ? theorem.conclusionFormula || formatFormula(theorem.ast) : theorem.formula;
      setMessage(`已选中定理：${theorem.formula}`, "good");
    });
    item.querySelector(".delete-theorem").addEventListener("click", () => deleteTheorem(theorem.id));
    el.theoremLibrary.appendChild(item);
  });
}

function deleteTheorem(theoremId) {
  const theorem = state.theorems.find((item) => item.id === theoremId);
  if (!theorem) return;
  const ok = window.confirm(`确定删除定理：${theorem.formula}？`);
  if (!ok) return;
  state.theorems = state.theorems
    .filter((item) => item.id !== theoremId)
    .map((item) => ({
      ...item,
      dependencies: (item.dependencies || []).filter((id) => id !== theoremId),
      proofSteps: (item.proofSteps || []).map((step) => (step.theoremId === theoremId ? { ...step, theoremId: null, detail: `${step.detail || ""}（引用定理已删除）` } : step)),
    }));
  persistTheorems();
  setMessage(`已删除定理：${theorem.formula}`, "good");
  if (el.dependencyGraphSection && !el.dependencyGraphSection.classList.contains("is-hidden")) {
    el.dependencyGraphSection.classList.add("is-hidden");
    renderTheoremDependencyGraph();
  }
  render();
}

function renderTheoremDependencyGraph() {
  el.dependencyGraphSection.classList.toggle("is-hidden");
  if (el.dependencyGraphSection.classList.contains("is-hidden")) {
    return;
  }
  el.theoremDependencyGraph.innerHTML = "";
  if (!state.theorems.length) {
    el.theoremDependencyGraph.innerHTML = `<div class="empty-state">定理库为空，暂无依赖关系。</div>`;
    return;
  }

  const idToIndex = new Map(state.theorems.map((theorem, index) => [theorem.id, index]));
  const levels = computeTheoremDepthLevels();
  const maxLevel = Math.max(0, ...levels);
  const levelBuckets = Array.from({ length: maxLevel + 1 }, () => []);
  levels.forEach((level, index) => {
    levelBuckets[level].push(index);
  });
  const maxRows = Math.max(1, ...levelBuckets.map((bucket) => bucket.length));
  const width = Math.max(920, (maxLevel + 1) * 330 + 80);
  const height = Math.max(300, maxRows * 170 + 80);
  const stage = document.createElement("div");
  stage.className = "dependency-stage";
  stage.style.width = `${width}px`;
  stage.style.height = `${height}px`;

  const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg.classList.add("graph-edges");
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  stage.appendChild(svg);

  const positions = state.theorems.map((_, index) => {
    const level = levels[index];
    const row = levelBuckets[level].indexOf(index);
    return {
      x: 40 + level * 330,
      y: 40 + row * 170,
    };
  });

  state.theorems.forEach((theorem, index) => {
    for (const dependencyId of theorem.dependencies || []) {
      const depIndex = idToIndex.get(dependencyId);
      if (depIndex === undefined) continue;
      const from = positions[depIndex];
      const to = positions[index];
      const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const startX = from.x + 260;
      const startY = from.y + 43;
      const endX = to.x;
      const endY = to.y + 43;
      const midX = (startX + endX) / 2;
      const dValue = `M ${startX} ${startY} C ${midX} ${startY}, ${midX} ${endY}, ${endX} ${endY}`;
      path.setAttribute("d", dValue);
      path.setAttribute("fill", "none");
      path.setAttribute("stroke", "#7a8b87");
      path.setAttribute("stroke-width", "2");
      svg.appendChild(path);

      const arrow = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const arrowX = midX;
      const arrowY = (startY + endY) / 2;
      const direction = endX >= startX ? 1 : -1;
      arrow.setAttribute(
        "d",
        `M ${arrowX + direction * 11} ${arrowY} L ${arrowX - direction * 8} ${arrowY - 8} L ${arrowX - direction * 8} ${arrowY + 8} Z`,
      );
      arrow.setAttribute("fill", "#7a8b87");
      arrow.setAttribute("opacity", "0.92");
      svg.appendChild(arrow);
    }
  });

  state.theorems.forEach((theorem, index) => {
    const node = document.createElement("div");
    node.className = "dependency-node";
    node.style.left = `${positions[index].x}px`;
    node.style.top = `${positions[index].y}px`;
    node.innerHTML = `<small>定理 ${index + 1}</small><code>${escapeHtml(theorem.formula)}</code>`;
    stage.appendChild(node);
  });
  el.theoremDependencyGraph.appendChild(stage);
}

function computeTheoremDepthLevels() {
  const idToIndex = new Map(state.theorems.map((theorem, index) => [theorem.id, index]));
  const memo = new Map();
  const visiting = new Set();

  function depth(index) {
    if (memo.has(index)) return memo.get(index);
    if (visiting.has(index)) return 0;
    visiting.add(index);
    const deps = (state.theorems[index].dependencies || [])
      .map((id) => idToIndex.get(id))
      .filter((item) => item !== undefined);
    const value = deps.length ? Math.max(...deps.map((depIndex) => depth(depIndex))) + 1 : 0;
    visiting.delete(index);
    memo.set(index, value);
    return value;
  }

  return state.theorems.map((_, index) => depth(index));
}

function renderTargetStatus() {
  if (!state.target) {
    el.targetStatus.textContent = "待开始";
    el.targetStatus.className = "status-pill neutral";
    el.saveTheoremBtn.disabled = true;
    el.enterDeductionBtn.disabled = true;
    el.exitDeductionBtn.disabled = true;
    return;
  }
  el.enterDeductionBtn.disabled = !state.currentGoal || state.currentGoal.ast.type !== "implies";
  el.exitDeductionBtn.disabled = state.deductionStack.length <= getFixedPremiseCount();
  if (isGoalProved()) {
    el.targetStatus.textContent = "已证明";
    el.targetStatus.className = "status-pill success";
    el.saveTheoremBtn.disabled = false;
    showAccepted();
  } else {
    el.targetStatus.textContent = "证明中";
    el.targetStatus.className = "status-pill warning";
    el.saveTheoremBtn.disabled = true;
  }
}

function showAccepted() {
  if (state.acceptedShown || !el.acceptedToast) return;
  state.acceptedShown = true;
  el.acceptedToast.classList.remove("show");
  void el.acceptedToast.offsetWidth;
  el.acceptedToast.classList.add("show");
}

function render() {
  renderProofTable();
  renderGraph();
  renderLibrary();
  renderPremiseOptions();
  renderDeductionStack();
  renderTheoremPremiseControls();
  renderTargetStatus();
}

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

function installEvents() {
  el.setTargetBtn.addEventListener("click", setTarget);
  el.targetInput.addEventListener("keydown", (event) => {
    if (event.key === "Enter") setTarget();
  });
  el.addStepBtn.addEventListener("click", addStep);
  el.checkCurrentBtn.addEventListener("click", checkCurrentInput);
  el.enterDeductionBtn.addEventListener("click", enterDeductionLayer);
  el.exitDeductionBtn.addEventListener("click", exitDeductionLayer);
  el.saveTheoremBtn.addEventListener("click", saveCurrentTheorem);
  el.loadDemoBtn.addEventListener("click", loadDemo);
  el.resetProofBtn.addEventListener("click", resetProof);
  el.dependencyGraphBtn.addEventListener("click", renderTheoremDependencyGraph);
  el.clearLibraryBtn.addEventListener("click", clearLibrary);
  el.sourceModes.forEach((item) => item.addEventListener("change", updateModeControls));
  el.premiseSelect.addEventListener("change", () => {
    const index = Number.parseInt(el.premiseSelect.value, 10);
    const premise = getTargetAssumptions()[index];
    if (premise) {
      el.formulaInput.value = premise.formula;
    }
  });
  el.theoremSelect.addEventListener("change", () => {
    const theorem = state.theorems.find((item) => item.id === el.theoremSelect.value);
    renderTheoremPremiseControls();
    if (theorem) {
      el.formulaInput.disabled = (theorem.premises || []).length > 0;
      el.formulaInput.value = (theorem.premises || []).length ? theorem.conclusionFormula || formatFormula(theorem.ast) : theorem.formula;
    }
  });
}

function boot() {
  axiomPatterns.forEach((axiom) => {
    axiom.ast = parseFormula(axiom.text);
  });
  loadTheorems();
  installEvents();
  setTarget();
  render();
}

boot();
