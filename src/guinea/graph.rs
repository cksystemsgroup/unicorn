use egui::DragValue;
use std::{borrow::Cow, collections::HashMap};

use crate::guinea::graph::ConcSymb::Concrete;
use crate::guinea::graph::Sort::{Bitvec, Boolean, Immediate};
use egui_node_graph::*;

#[derive(Clone, Debug, Copy, Hash, Eq, PartialEq)]
pub enum ConcSymb {
    Concrete(u64),
    // Symbolic(u64),
}

#[derive(Clone, Debug)]
pub enum Sort {
    Boolean(bool),
    Bitvec(ConcSymb),
    String(String),
    Array(HashMap<ConcSymb, ConcSymb>),
    Immediate(u64),
    Error,
}

impl Default for Sort {
    fn default() -> Self {
        Bitvec(ConcSymb::Concrete(0))
    }
}

impl Sort {
    fn default_bool() -> Self {
        Boolean(false)
    }

    fn default_array() -> Self {
        Self::Array(HashMap::new())
    }

    fn default_string() -> Self {
        Self::String("no name".to_string())
    }

    fn default_imm() -> Self {
        Immediate(0)
    }
}

#[derive(Debug)]
pub struct BeatorNodeData {
    pub template: BeatorTemplate,
    pub x: usize,
    pub y: usize,
    pub sort: Sort,
}

#[derive(PartialEq, Eq)]
pub enum BeatorDataType {
    Sort,
}

#[derive(Clone, Debug)]
pub enum BeatorValueType {
    Sort { value: Sort },
}

impl Default for BeatorValueType {
    fn default() -> Self {
        // NOTE: This is just a dummy `Default` implementation. The library
        // requires it to circumvent some internal borrow checker issues.
        Self::Sort {
            value: Sort::Bitvec(ConcSymb::Concrete(0)),
        }
    }
}

impl BeatorValueType {
    pub fn try_to_sort(self) -> anyhow::Result<Sort> {
        let BeatorValueType::Sort { value } = self;
        Ok(value)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BeatorTemplate {
    MemoryConst,
    Const,
    Read,
    Write,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Sll,
    Srl,
    Ult,
    Ext,
    Ite,
    Eq,
    And,
    Not,
    State,
    Next,
    Input,
    Bad,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeatorResponse {
    SetActiveNode(NodeId),
    ClearActiveNode,
}

#[derive(Default)]
pub struct BeatorGraphState {
    pub active_node: Option<NodeId>,
    pub nid_map: HashMap<usize, NodeId>,
    pub sort_map: HashMap<usize, Sort>,
}

impl DataTypeTrait<BeatorGraphState> for BeatorDataType {
    fn data_type_color(&self, _user_state: &mut BeatorGraphState) -> egui::Color32 {
        match self {
            BeatorDataType::Sort => egui::Color32::from_rgb(255, 0, 0),
        }
    }

    fn name(&self) -> Cow<'_, str> {
        match self {
            BeatorDataType::Sort => Cow::Borrowed("Sort"),
        }
    }
}

impl NodeTemplateTrait for BeatorTemplate {
    type NodeData = BeatorNodeData;
    type DataType = BeatorDataType;
    type ValueType = BeatorValueType;
    type UserState = BeatorGraphState;

    fn node_finder_label(&self, _user_state: &mut Self::UserState) -> Cow<'_, str> {
        Cow::Borrowed(match self {
            BeatorTemplate::Const => "Const",
            BeatorTemplate::Read => "Read",
            BeatorTemplate::Write => "Write",
            BeatorTemplate::Add => "Addition",
            BeatorTemplate::Sub => "Subtraction",
            BeatorTemplate::Mul => "Multiplication",
            BeatorTemplate::Div => "Division",
            BeatorTemplate::Rem => "Remainder",
            BeatorTemplate::Sll => "Shift Left Logically",
            BeatorTemplate::Srl => "Shift Right Logically",
            BeatorTemplate::Ult => "Less than",
            BeatorTemplate::Ext => "Extend",
            BeatorTemplate::Ite => "If-then-else",
            BeatorTemplate::Eq => "Equality",
            BeatorTemplate::And => "And",
            BeatorTemplate::Not => "Not",
            BeatorTemplate::State => "State",
            BeatorTemplate::Next => "Next",
            BeatorTemplate::Input => "Input",
            BeatorTemplate::Bad => "Bad",
            BeatorTemplate::MemoryConst => "Const (Memory)",
        })
    }

    fn node_graph_label(&self, user_state: &mut Self::UserState) -> String {
        // It's okay to delegate this to node_finder_label if you don't want to
        // show different names in the node finder and the node itself.
        self.node_finder_label(user_state).into()
    }

    fn user_data(&self, _user_state: &mut Self::UserState) -> Self::NodeData {
        BeatorNodeData {
            template: *self,
            x: 0,
            y: 0,
            sort: Sort::default(),
        }
    }

    fn build_node(
        &self,
        graph: &mut Graph<Self::NodeData, Self::DataType, Self::ValueType>,
        _user_state: &mut Self::UserState,
        node_id: NodeId,
    ) {
        let input_sort = |graph: &mut BeatorGraph, name: &str, val: Sort| {
            graph.add_input_param(
                node_id,
                name.to_string(),
                BeatorDataType::Sort,
                BeatorValueType::Sort { value: val },
                InputParamKind::ConnectionOrConstant,
                true,
            );
        };

        let output_sort = |graph: &mut BeatorGraph, name: &str| {
            graph.add_output_param(node_id, name.to_string(), BeatorDataType::Sort);
        };

        match self {
            BeatorTemplate::Const => {
                graph.add_input_param(
                    node_id,
                    "Immediate".to_string(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
                output_sort(graph, "Output");
            }
            BeatorTemplate::Read => {
                input_sort(graph, "Memory", Sort::default_array());
                input_sort(graph, "Address", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Write => {
                input_sort(graph, "Memory", Sort::default_array());
                input_sort(graph, "Address", Sort::default());
                input_sort(graph, "Value", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Add
            | BeatorTemplate::Sub
            | BeatorTemplate::Mul
            | BeatorTemplate::Div
            | BeatorTemplate::Rem
            | BeatorTemplate::Sll
            | BeatorTemplate::Srl
            | BeatorTemplate::Ult => {
                input_sort(graph, "Left", Sort::default());
                input_sort(graph, "Right", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Ext => {
                input_sort(graph, "From", Sort::default());
                input_sort(graph, "Value", Sort::default_imm());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Ite => {
                input_sort(graph, "Condition", Sort::default_bool());
                input_sort(graph, "Left", Sort::default());
                input_sort(graph, "Right", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::Eq => {
                input_sort(graph, "Left", Sort::default());
                input_sort(graph, "Right", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::And => {
                input_sort(graph, "Left", Sort::default());
                input_sort(graph, "Right", Sort::default());
                output_sort(graph, "Output");
            }

            BeatorTemplate::Not => {
                input_sort(graph, "Value", Sort::default());
                output_sort(graph, "Output");
            }
            BeatorTemplate::State => {
                input_sort(graph, "Initial Value", Sort::default());
                graph.add_input_param(
                    node_id,
                    "Name".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default_string(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
                output_sort(graph, "Output")
            }
            BeatorTemplate::Next => {
                input_sort(graph, "State", Sort::default());
                input_sort(graph, "Next", Sort::default());
            }
            BeatorTemplate::Input => {
                graph.add_input_param(
                    node_id,
                    "Value".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
                graph.add_input_param(
                    node_id,
                    "Name".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default_string(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
            }
            BeatorTemplate::Bad => {
                input_sort(graph, "Condition", Sort::default_bool());
                graph.add_input_param(
                    node_id,
                    "Name".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default_string(),
                    },
                    InputParamKind::ConstantOnly,
                    true,
                );
                output_sort(graph, "Output");
            }
            BeatorTemplate::MemoryConst => {
                graph.add_input_param(
                    node_id,
                    "Immediate".into(),
                    BeatorDataType::Sort,
                    BeatorValueType::Sort {
                        value: Sort::default_array(),
                    },
                    InputParamKind::ConstantOnly,
                    false,
                );
                output_sort(graph, "Output");
            }
        }
    }
}

pub struct AllBeatorNodeTemplates;

impl NodeTemplateIter for AllBeatorNodeTemplates {
    type Item = BeatorTemplate;

    fn all_kinds(&self) -> Vec<Self::Item> {
        vec![
            BeatorTemplate::Const,
            BeatorTemplate::MemoryConst,
            BeatorTemplate::Read,
            BeatorTemplate::Write,
            BeatorTemplate::Add,
            BeatorTemplate::Sub,
            BeatorTemplate::Mul,
            BeatorTemplate::Div,
            BeatorTemplate::Rem,
            BeatorTemplate::Sll,
            BeatorTemplate::Srl,
            BeatorTemplate::Ult,
            BeatorTemplate::Ext,
            BeatorTemplate::Ite,
            BeatorTemplate::Eq,
            BeatorTemplate::And,
            BeatorTemplate::Not,
            BeatorTemplate::State,
            BeatorTemplate::Next,
            BeatorTemplate::Input,
            BeatorTemplate::Bad,
        ]
    }
}

impl WidgetValueTrait for BeatorValueType {
    type Response = BeatorResponse;
    type UserState = BeatorGraphState;
    type NodeData = BeatorNodeData;
    fn value_widget(
        &mut self,
        param_name: &str,
        _node_id: NodeId,
        ui: &mut egui::Ui,
        _user_state: &mut BeatorGraphState,
        _node_data: &BeatorNodeData,
    ) -> Vec<BeatorResponse> {
        match self {
            BeatorValueType::Sort { value } => match value {
                Boolean(val) => {
                    ui.label(param_name);
                    ui.checkbox(val, "value");
                }
                Bitvec(val) => match val {
                    Concrete(x) => {
                        ui.label(param_name);
                        ui.add(DragValue::new(x));
                    }
                },
                Sort::String(val) => {
                    ui.label(val.as_str());
                }
                Sort::Array(_) => {
                    ui.label("Virtual Memory");
                }
                Immediate(val) => {
                    ui.label(format!("Extend by {val}"));
                }
                Sort::Error => {
                    ui.label("Error Input");
                }
            },
        }
        Vec::new()
    }
}

impl UserResponseTrait for BeatorResponse {}

impl NodeDataTrait for BeatorNodeData {
    type Response = BeatorResponse;
    type UserState = BeatorGraphState;
    type DataType = BeatorDataType;
    type ValueType = BeatorValueType;

    fn bottom_ui(
        &self,
        ui: &mut egui::Ui,
        node_id: NodeId,
        _graph: &Graph<BeatorNodeData, BeatorDataType, BeatorValueType>,
        user_state: &mut Self::UserState,
    ) -> Vec<NodeResponse<BeatorResponse, BeatorNodeData>>
    where
        BeatorResponse: UserResponseTrait,
    {
        let mut responses = vec![];
        let is_active = user_state
            .active_node
            .map(|id| id == node_id)
            .unwrap_or(false);

        if !is_active {
            if ui.button("👁 Set active").clicked() {
                responses.push(NodeResponse::User(BeatorResponse::SetActiveNode(node_id)));
            }
        } else {
            let button =
                egui::Button::new(egui::RichText::new("👁 Active").color(egui::Color32::BLACK))
                    .fill(egui::Color32::GOLD);
            if ui.add(button).clicked() {
                responses.push(NodeResponse::User(BeatorResponse::ClearActiveNode));
            }
        }

        responses
    }
}

pub type BeatorGraph = Graph<BeatorNodeData, BeatorDataType, BeatorValueType>;
pub type BeatorEditorState = GraphEditorState<
    BeatorNodeData,
    BeatorDataType,
    BeatorValueType,
    BeatorTemplate,
    BeatorGraphState,
>;

#[derive(Default)]
pub struct NodeGraph {
    pub state: BeatorEditorState,

    pub user_state: BeatorGraphState,
    pub out: String,
    pub y_lookup: Vec<usize>,
}

impl NodeGraph {
    pub fn lookup_y_and_inc(&mut self, x: usize) -> usize {
        if let Some(y) = self.y_lookup.get(x) {
            let ret = *y;
            *self.y_lookup.get_mut(x).unwrap() += 1;
            ret
        } else {
            self.y_lookup.push(1);
            0
        }
    }
}

type OutputsCache = HashMap<OutputId, BeatorValueType>;

/// Recursively evaluates all dependencies of this node, then evaluates the node itself.
pub fn evaluate_node(
    graph: &BeatorGraph,
    node_id: NodeId,
    outputs_cache: &mut OutputsCache,
) -> anyhow::Result<BeatorValueType> {
    struct Evaluator<'a> {
        graph: &'a BeatorGraph,
        outputs_cache: &'a mut OutputsCache,
        node_id: NodeId,
    }
    impl<'a> Evaluator<'a> {
        fn new(
            graph: &'a BeatorGraph,
            outputs_cache: &'a mut OutputsCache,
            node_id: NodeId,
        ) -> Self {
            Self {
                graph,
                outputs_cache,
                node_id,
            }
        }
        fn evaluate_input(&mut self, name: &str) -> anyhow::Result<BeatorValueType> {
            evaluate_input(self.graph, self.node_id, name, self.outputs_cache)
        }
        fn populate_output(
            &mut self,
            name: &str,
            value: BeatorValueType,
        ) -> anyhow::Result<BeatorValueType> {
            populate_output(self.graph, self.outputs_cache, self.node_id, name, value)
        }
        fn input_sort(&mut self, name: &str) -> anyhow::Result<Sort> {
            self.evaluate_input(name)?.try_to_sort()
        }
        fn output_sort(&mut self, name: &str, value: Sort) -> anyhow::Result<BeatorValueType> {
            self.populate_output(name, BeatorValueType::Sort { value })
        }
    }

    let node = &graph[node_id];
    let mut evaluator = Evaluator::new(graph, outputs_cache, node_id);
    match node.user_data.template {
        BeatorTemplate::Const => {
            let value = evaluator.input_sort("Immediate")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::Read => {
            let memory = evaluator.input_sort("Memory")?;
            let address = evaluator.input_sort("Address")?;

            match (memory, address) {
                (Sort::Array(mem), Bitvec(add)) => {
                    evaluator.output_sort("Output", Bitvec(*mem.get(&add).unwrap_or(&Concrete(0))))
                }
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Write => {
            let memory = evaluator.input_sort("Memory")?;
            let address = evaluator.input_sort("Address")?;
            let value = evaluator.input_sort("Value")?;

            match (memory, address, value) {
                (Sort::Array(mut mem), Bitvec(add), Bitvec(val)) => {
                    mem.insert(add, val);
                    evaluator.output_sort("Output", Sort::Array(mem))
                }
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Add => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l + r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Sub => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l - r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Mul => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l * r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Div => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l / r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Rem => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l % r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Sll => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l << r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Srl => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l >> r)))
                    }
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Ult => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => evaluator.output_sort("Output", Boolean(l < r)),
                },
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Ext => {
            let input = evaluator.input_sort("From")?;
            let value = evaluator.input_sort("Value")?;
            match (input, value) {
                (Bitvec(i), Immediate(_)) => evaluator.output_sort("Output", Bitvec(i)),
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Ite => {
            let cond = evaluator.input_sort("Condition")?;
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;

            if let Boolean(cond) = cond {
                evaluator.output_sort("Output", if cond { left } else { right })
            } else {
                Ok(BeatorValueType::Sort { value: Sort::Error })
            }
        }
        BeatorTemplate::Eq => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;

            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => evaluator.output_sort("Output", Boolean(l == r)),
                },
                (Boolean(l), Boolean(r)) => evaluator.output_sort("Output", Boolean(l == r)),
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::And => {
            let left = evaluator.input_sort("Left")?;
            let right = evaluator.input_sort("Right")?;
            match (left, right) {
                (Bitvec(l), Bitvec(r)) => match (l, r) {
                    (Concrete(l), Concrete(r)) => {
                        evaluator.output_sort("Output", Bitvec(Concrete(l & r)))
                    }
                },
                (Boolean(l), Boolean(r)) => evaluator.output_sort("Output", Boolean(l && r)),
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::Not => {
            let value = evaluator.input_sort("Value")?;
            match value {
                Boolean(val) => evaluator.output_sort("Output", Boolean(!val)),
                _ => Ok(BeatorValueType::Sort { value: Sort::Error }),
            }
        }
        BeatorTemplate::State => {
            let value = evaluator.input_sort("Initial Value")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::Next => {
            let value = evaluator.input_sort("Value")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::Input => {
            let value = evaluator.input_sort("Value")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::Bad => {
            let value = evaluator.input_sort("Condition")?;
            evaluator.output_sort("Output", value)
        }
        BeatorTemplate::MemoryConst => {
            let value = evaluator.input_sort("Immediate")?;
            evaluator.output_sort("Output", value)
        }
    }
}

fn populate_output(
    graph: &BeatorGraph,
    outputs_cache: &mut OutputsCache,
    node_id: NodeId,
    param_name: &str,
    value: BeatorValueType,
) -> anyhow::Result<BeatorValueType> {
    let output_id = graph[node_id].get_output(param_name)?;
    outputs_cache.insert(output_id, value.clone());
    Ok(value)
}

// Evaluates the input value of
fn evaluate_input(
    graph: &BeatorGraph,
    node_id: NodeId,
    param_name: &str,
    outputs_cache: &mut OutputsCache,
) -> anyhow::Result<BeatorValueType> {
    let input_id = graph[node_id].get_input(param_name)?;

    if let Some(other_output_id) = graph.connection(input_id) {
        if let Some(other_value) = outputs_cache.get(&other_output_id) {
            Ok(other_value.clone())
        } else {
            evaluate_node(graph, graph[other_output_id].node, outputs_cache)?;

            let val = outputs_cache
                .get(&other_output_id)
                .expect("Cache should be populated")
                .clone();
            Ok(val)
        }
    } else {
        Ok(graph[input_id].value.clone())
    }
}
