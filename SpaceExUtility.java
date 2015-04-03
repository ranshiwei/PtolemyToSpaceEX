/* An utility function for traversing the system and generate files for model checking using Regional Decision Diagram (RED).

 Copyright (c) 1998-2010 The Regents of the University of California.
 All rights reserved.
 Permission is hereby granted, without written agreement and without
 license or royalty fees, to use, copy, modify, and distribute this
 software and its documentation for any purpose, provided that the above
 copyright notice and the following two paragraphs appear in all copies
 of this software.

 IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY
 FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES
 ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF
 THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY OF
 SUCH DAMAGE.

 THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES,
 INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE
 PROVIDED HEREUNDER IS ON AN "AS IS" BASIS, AND THE UNIVERSITY OF
 CALIFORNIA HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES,
 ENHANCEMENTS, OR MODIFICATIONS.

 PT_COPYRIGHT_VERSION_2
 COPYRIGHTENDKEY

 */
package ptolemy.verification.kernel;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

import org.python.modules.newmodule;

import ptolemy.domains.continuous.lib.Integrator;
import ptolemy.domains.continuous.lib.LevelCrossingDetector;
import ptolemy.actor.lib.Const;
import ptolemy.actor.CompositeActor;
import ptolemy.actor.Director;
import ptolemy.actor.IOPort;
import ptolemy.actor.TypedActor;
import ptolemy.actor.TypedIOPort;
import ptolemy.domains.continuous.kernel.ContinuousDirector;
import ptolemy.domains.modal.modal.ModalModel;
import ptolemy.domains.modal.modal.RefinementPort;
import ptolemy.kernel.ComponentPort;
import ptolemy.kernel.Entity;
import ptolemy.kernel.Port;
import ptolemy.kernel.util.IllegalActionException;
import ptolemy.kernel.util.NameDuplicationException;
import ptolemy.kernel.util.NamedObj;

import ptolemy.domains.modal.kernel.FSMActor;
import ptolemy.domains.modal.kernel.State;
import ptolemy.domains.modal.kernel.Transition;
public class SpaceExUtility{
    
   
    /**
     * This is the main function which generates the system description
     * which is acceptable by the tool SpaceEx.
     * <p>
     * For hierarchical conversion, here we are able to deal with cases where
     * state refinement exists. For a modalmodel with state refinement, we first
     * rewrite it into an equivalent FSMActor.
     *
     * @param PreModel The original model in Ptolemy II
     *
     */
    public static StringBuffer generateSpaceExDescription(CompositeActor PreModel)
            throws IllegalActionException,
            NameDuplicationException, CloneNotSupportedException
    {
    	StringBuffer returnSEFormat = new StringBuffer("");
    

        _variableInfoMap = new HashMap<String, HashMap<String,VariableInfo>>();
        _signalPort = new ArrayList<String>();
        
        _newguardMap = new HashMap<String, HashMap<String,List<String>>>();
        
        _levelcrossMap = new HashMap<String, HashMap<String,List<String>>>();
        _setinfoMap = new HashMap<String, HashMap<String,String>>();
        _changedsignallabelMap = new HashMap<String, HashMap<Transition,String>>();
        _guardExprMap = new HashMap<String, HashMap<Transition,String>>();
        _signalportMap = new HashMap<String, List<String>>();
        _integratorMap = new HashMap<String, HashMap<String,List<String>>>();
        _constMap = new HashMap<String, HashMap<String,String>>();
        _modalmodel = new String[scope][scope];
        for(int i = 0; i < scope; i++)
        {
            for(int j = 0;j < scope; j++)
                _modalmodel[i][j] = "";
        }
        
        //Perform a scan of the whole system in order to retrieve signals
        // used in the system and their locations/visibilities for later
        // analysis

        _prescanSystemSignal(PreModel,new HashMap<String, SpaceExUtility.VariableInfo>());
        
        
        returnSEFormat.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>  \n" );
        returnSEFormat.append("<sspaceex xmlns=\"http://www-verimag.imag.fr/xml-namespaces/sspaceex\"" +
                        " version=\"0.2\" math=\"SpaceEx\">  \n");
        //Generate  base Component descriptions
        returnSEFormat.append(generateBaseComponent());
        
        //Generate the network Component descriptions
        returnSEFormat.append(generateNetworkComponent());
        
        returnSEFormat.append("</sspaceex>");
        
        return returnSEFormat;
    }
    
    private static String generateBaseComponent()
    {
        StringBuilder mainbaseComponent = new StringBuilder("");
        //There may more than one ModalModel in the Model,so we deal with
        //it in a For cycle.
        for(int i = 0; i < ModalModelnum; i++)
        {
            int position = 0;
            StringBuilder baseComponent = new StringBuilder("");
            String simplifyComponent = _modalmodel[i+1][0];
            simplifyComponent = simplifyComponent.replace(" ", "");
            baseComponent.append("  <component id=\""+simplifyComponent+"\">  \n");
            
            HashMap<String, List<String>> _guardInfo = new HashMap<String, List<String>>();
            HashMap<Transition, String> _presentSignal = new HashMap<Transition, String>();
            HashMap<String, VariableInfo> _variableInfo = new HashMap<String, SpaceExUtility.VariableInfo>();
            _variableInfo = _variableInfoMap.get(simplifyComponent);
            
            Set<String> variableSet = _variableInfo.keySet();
            for(int m = 0 ;m <= _modalmodel[i+1].length;m++)
            {
                 if(_modalmodel[i+1][m].length() == 0)
                 {
                     position = m-1;
                     break;
                 }
            }
            
            for(int j = 0; j <= position; j++)
            {
                
                Set<String> constSet = _constMap.get(_modalmodel[i+1][j]).keySet();
                Iterator<String> itconst = constSet.iterator();
                String[] tempSet = new String[scope];
                int num = 0;
                while(itconst.hasNext())
                {
                    tempSet[num++]=itconst.next().toString();
                }
               
                Iterator<String> newitconst = constSet.iterator();
                while(newitconst.hasNext())
                {
                    baseComponent.append("    <param name=\""+newitconst.next()+"\" type=\"real\" local=\"false\"" +
                                    " d1=\"1\" d2=\"1\" dynamics=\"const\" />  \n");
                }
                
                //remove all the const in the variableSet,only leaves the variable
                for(int k = 0; k < tempSet.length; k++)
                {
                    variableSet.remove(tempSet[k]);
                }
            }
            
            Iterator<String> newitvariable = variableSet.iterator();
            
            while(newitvariable.hasNext())
            {
                String variable = newitvariable.next();
                baseComponent.append("    <param name=\""+variable+"\" type=\"real\" local=\"false\"" +
                                " d1=\"1\" d2=\"1\" dynamics=\"any\" />  \n");
            }
            
            HashMap<Transition, String> _guardExpr = new HashMap<Transition, String>();
            _guardExpr = _guardExprMap.get(_modalmodel[i+1][0]);
            
            if(_guardExpr.size() == 0)
            {}else {
                Set<Transition> guardtrans = _guardExpr.keySet();
                Iterator<Transition> itguard = guardtrans.iterator();
                List<String> presentlist = new ArrayList<String>();
                
                while (itguard.hasNext()) {
                    boolean temp = true;
                    Transition guardTransition = itguard.next();
                    String guardExpression = guardTransition.getGuardExpression();
                    String storeExpression = null;
                    
                    //Handle the duplicate signal present in a modalmodel,
                    //we will use the signal as a transition's label ,so it cannot be
                    //the same name ,so for the second present ,we add "_0" at the end of
                    //it,and "_1" for the third and so on
                    for (int j = 0; j < _signalPort.size(); j++) {
                        if(guardExpression.equals(_signalPort.get(j)+"_isPresent"))
                        {
                            storeExpression = new String(_signalPort.get(j));
                            for (int k = 0; k < presentlist.size(); k++) {
                                if (storeExpression.equals(presentlist.get(k))) {
                                    storeExpression = presentlist.get(j)+"_"+(presentlist.size()-1);
                                    
                                }
                            }
                            baseComponent.append("    <param name=\""+storeExpression+"\" type=\"label\" local=\"false\" /> \n");
                            _presentSignal.put(guardTransition, storeExpression);
                            
                            temp = false;
                            presentlist.add(storeExpression);
                        }
                    }
                    // if the guard is not "XX_isPressent",we may try to analyse the destination state,
                    //ergodic their actor,if the "output" port or "state" port connected to a refinementPort
                    //we would make the refinementPort as the lable'name 
                    if(temp)
                    {
                        State destState = guardTransition.destinationState();
                        String presentLabel = "";
                        String refinementList = ((State) destState).refinementName
                                .getExpression();
                        if ((refinementList == null)
                                || (refinementList.equalsIgnoreCase(""))) {
                        } else {
                            TypedActor[] refinementSystemActors;
                            try {
                                refinementSystemActors = ((State) destState)
                                        .getRefinement();
                                if (refinementSystemActors != null) {
                                    if (refinementSystemActors.length == 1) {
                                        
                                        TypedActor innerActor = refinementSystemActors[0];
                                        if (innerActor instanceof FSMActor) {
                                            //FSMActor innerFSMActor = (FSMActor) innerActor;

                                        } else if (innerActor instanceof CompositeActor) 
                                        {
                                            for (Iterator actors = (((CompositeActor) innerActor).entityList())
                                                    .iterator(); actors.hasNext();) {
                                                Entity innerEntity = (Entity) actors.next();
                                                
                                                Iterator<?> ports = innerEntity.portList().iterator();
                                                
                                                while (ports.hasNext()) {
                                                    Port port = (Port) ports.next();

                                                    List<Port> farport = port.connectedPortList();
                                                    
                                                    if(port.getName().equals("output") || port.getName().equals("state"))
                                                    {
                                                        Iterator<Port> sinkport = farport.iterator();
                                                        while(sinkport.hasNext())
                                                        {
                                                            Port statePort = sinkport.next();
                                                            if(statePort instanceof RefinementPort)
                                                            {
                                                                presentLabel = statePort.getName();
                                                            }else if(statePort instanceof TypedIOPort)
                                                            {
                                                                
                                                            }
                                                        }
                                                    }
                                                } 
                                            }
                                        }
                                     }
                                }
                            } catch (IllegalActionException e) {
                                e.printStackTrace();
                            }
                        }
                        baseComponent.append("    <param name=\""+presentLabel+"\" type=\"label\" local=\"false\" /> \n");
                        _presentSignal.put(guardTransition, presentLabel);
                    }
                }
                _changedsignallabelMap.put(_modalmodel[i+1][0], _presentSignal);
            }
                
            for(int j = 1; j <= position; j++)
            {
                baseComponent.append("    <location id=\""+j+"\" name=\""+_modalmodel[i+1][j]+
                        "\" x=\""+(150+50*j)+"\" y=\""+(120+40*j)+"\" width=\"200.0\" height=\"123.0\">  \n");
                StringBuffer bfvariant = new StringBuffer("");
                String invariant = "";
                HashMap<String, List<String>> innerguardHash = _newguardMap.get(_modalmodel[i+1][0]);
                List<String> innerguard = innerguardHash.get(_modalmodel[i+1][j]);
                
                if(innerguard != null && position > 1){
                    for(int k = 0; k < innerguard.size(); k++)
                    {
                       if((k+1) == innerguard.size())
                           bfvariant.append(innerguard.get(k));
                       else 
                           bfvariant.append(innerguard.get(k)+" &amp ");
                    }
                    //To exchange "<" or ">"
                    invariant = bfvariant.toString();
                    invariant = invariant.replace("&gt;", "@@");
                    invariant = invariant.replace("&lt;", "$$");
                    invariant = invariant.replace("$$", "&gt;");
                    invariant = invariant.replace("@@", "&lt;");
                    
                    baseComponent.append("        <invariant>"+invariant+"</invariant>  \n");
                }
                else {
                    HashMap<String, List<String>> levelcrossMap = _levelcrossMap.get(_modalmodel[i+1][0]);
                    List<String> othinnerguard = levelcrossMap.get(_modalmodel[i+1][j]);
                    if(othinnerguard != null){
                        for(int k = 0; k < othinnerguard.size(); k++)
                        {
                           if((k+1) == othinnerguard.size())
                               bfvariant.append(othinnerguard.get(k));
                           else 
                               bfvariant.append(othinnerguard.get(k)+" &amp ");
                        }
                        
                        invariant = bfvariant.toString();
                        baseComponent.append("        <invariant>"+invariant+"</invariant>  \n");
                    }
                }
                
                StringBuffer flowBuffer = new StringBuffer();
                HashMap<String, List<String>> IntegratorHash = new HashMap<String, List<String>>();
                IntegratorHash = _integratorMap.get(_modalmodel[i+1][0]);
                List<String> Integrator = new ArrayList<String>();
                Integrator = IntegratorHash.get(_modalmodel[i+1][j]);
                
                if(Integrator != null)
                {
                    for(int k = 0; k < Integrator.size(); k++)
                    {
                        if((k+1) == Integrator.size())
                            flowBuffer.append(Integrator.get(k));
                        else 
                            flowBuffer.append(Integrator.get(k)+" &amp; ");
                    }
                    baseComponent.append("        <flow>"+ flowBuffer +"</flow>  \n");
                }
                
                baseComponent.append("    </location>  \n");
            }
            Set<Transition> guardExpr = _guardExpr.keySet();
            Iterator<Transition> ittranstion = guardExpr.iterator();
                        
            while(ittranstion.hasNext())
            {
                Transition trans = (Transition)ittranstion.next();
                StringBuffer transitionBuffer = new StringBuffer();
                int sourceNum = -1,destinationNum = -1;
                String source = "", destination = "";
                destination = trans.destinationState().getName();
                source = trans.sourceState().getName();
                
                for(int k = 1; k <= position ; k++)
                {
                    if(source.equals(_modalmodel[i+1][k]))
                        sourceNum = k;
                    if(destination.equals(_modalmodel[i+1][k]))
                        destinationNum = k;
                }
               
                transitionBuffer.append("    <transition source=\""+sourceNum+"\" target=\""+destinationNum+"\">  \n");
                
                if(_changedsignallabelMap.size() == 0)
                {}else {
                    HashMap<Transition, String> newLabelHash = _changedsignallabelMap.get(_modalmodel[i+1][0]);
                    String newLabel = newLabelHash.get(trans); 
                    transitionBuffer.append("        <label>"+newLabel+"</label>  \n");                  
                    
                }
                _guardInfo = _newguardMap.get(_modalmodel[i+1][0]);
                List<String> guardInfo = _guardInfo.get(source);
                
                if(guardInfo != null)
                {
                    Iterator<String> itguard = guardInfo.iterator();
                    if(itguard.hasNext()) {
                        String attribute = itguard.next();
                        transitionBuffer.append("        <guard>"+attribute +"</guard>   \n");
                    } 
                }else {
                    StringBuffer reverseguard = new StringBuffer("");
                    HashMap<String, List<String>> levelcrossMap = _levelcrossMap.get(_modalmodel[i+1][0]);
                    List<String> innerguard = levelcrossMap.get(source);
                    if(innerguard != null)
                    {
                        for(int k = 0; k < innerguard.size(); k++)
                        {
                           if((k+1) == innerguard.size())
                               reverseguard.append(innerguard.get(k));
                           else 
                               reverseguard.append(innerguard.get(k)+" &amp ");
                        }
                    String reverse = reverseguard.toString();
                    reverse = reverse.replace("&gt;", "@@");
                    reverse = reverse.replace("&lt;", "$$");
                    reverse = reverse.replace("$$", "&gt;");
                    reverse = reverse.replace("@@", "&lt;");
                    transitionBuffer.append("        <guard>"+reverse +"</guard>   \n");  
                    }
                }
                HashMap<String, String> setinfo = _setinfoMap.get(_modalmodel[i+1][0]);         
                String setinfoString = setinfo.get(trans.getName());
                if (setinfoString != null) {
                    transitionBuffer.append("        <assignment>"+setinfoString+"</assignment>  \n");
                }
               
                transitionBuffer.append("    </transition>  \n");
                
                baseComponent.append(transitionBuffer);
            }
            baseComponent.append("  </component>   \n");
            mainbaseComponent.append(baseComponent);
        }
        StringBuffer timeBuffer = new StringBuffer();
        timeBuffer.append("  <component id=\"timer_template\">   \n");
        timeBuffer.append("    <param name=\"t\" type=\"real\" local=\"false\" d1=\"1\" d2=\"1\" dynamics=\"any\" />  \n");
        timeBuffer.append("    <location id=\"1\" name=\"running\" x=\"149.0\" y=\"110.0\">  \n");
        timeBuffer.append("      <flow>t'==1</flow>  \n");
        timeBuffer.append("    </location>  \n");
        timeBuffer.append("  </component>  \n");
        mainbaseComponent.append(timeBuffer);
        
        return mainbaseComponent.toString();
    }
    
    private static String generateNetworkComponent()
    {
        
        StringBuilder networkComponent = new StringBuilder("");
        networkComponent.append("  <component id=\"system\">   \n");
        List<String> duList = new ArrayList<String>();
        
        for (int i = 0; i < ModalModelnum; i++) {
            
            String simplifyComponent = _modalmodel[i+1][0];
            simplifyComponent = simplifyComponent.replace(" ", "");
            HashMap<String, VariableInfo> _variableInfo = _variableInfoMap.get(simplifyComponent);
            Set<String> variable = _variableInfo.keySet();
            Iterator<String> itvariable = variable.iterator();
            
            while (itvariable.hasNext()) {
                boolean ignoreDu = true;
                String localVariable = itvariable.next();
                for (int j = 0; j < duList.size(); j++) {
                    if (localVariable.equals(duList.get(j)))
                        ignoreDu = false;
                }
                if(ignoreDu)
                {
                    networkComponent.append("    <param name=\""+localVariable+"\" type=\"real\" local=\"false\" " +
                            "d1=\"1\" d2=\"1\" dynamics=\"any\" controlled=\"true\" />   \n");
                    duList.add(localVariable);
                }
            }
            
            HashMap<Transition, String> _guardLabel = new HashMap<Transition, String>();
            _guardLabel = _changedsignallabelMap.get(_modalmodel[i+1][0]);
            
            if (_guardLabel.size() == 0) {}
            else {
                Set<Transition> guardtrans = _guardLabel.keySet();
                Iterator<Transition> itguard = guardtrans.iterator();
                while (itguard.hasNext()) {
                    boolean ignoreDu = true;
                    String guardname = _guardLabel.get(itguard.next());
                    for (int j = 0; j < duList.size(); j++) {
                        if (guardname.equals(duList.get(j)))
                            ignoreDu = false;
                    }
                    if(ignoreDu)
                    {
                        networkComponent.append("    <param name=\""+guardname+"\" type=\"label\" local=\"false\" />   \n"); 
                        duList.add(guardname);
                    }
                }
            }
        }
        
        StringBuffer timeBuffer = new StringBuffer();
        timeBuffer.append("    <param name=\"t\" type=\"real\" local=\"false\" d1=\"1\" d2=\"1\" dynamics=\"any\" controlled=\"true\"  /> \n");
        
        networkComponent.append(timeBuffer);
        
        for(int i = 0; i < ModalModelnum; i++)
        {
            int position = 0;
            
            for(int m = 0 ;m <= _modalmodel[i+1].length;m++)
            {
                    if(_modalmodel[i+1][m].length() == 0)
                    {
                        position = m-1;
                        break;
                    }
            }
            StringBuilder innerComponent = new StringBuilder("");
            String simplifyComponent = _modalmodel[i+1][0];
            simplifyComponent = simplifyComponent.replace(" ", "");
            HashMap<String, VariableInfo> _variableInfo = _variableInfoMap.get(simplifyComponent);
            Set<String> variable = _variableInfo.keySet();
                
            innerComponent.append("    <bind component=\""+simplifyComponent+"\" " +
            		"as=\""+simplifyComponent+"\" x=\"238.0\" y=\"106.0\">  \n");
            Iterator<String> newitvariable = variable.iterator();
            
            for(int j = 0; j <= position; j++)
            {
                Set<String> constSet = _constMap.get(_modalmodel[i+1][j]).keySet();
                Iterator<String> itconst = constSet.iterator();
                
                while (itconst.hasNext()) {
                    String constname = itconst.next();
                    innerComponent.append("      <map key=\""+constname+"\">"+_constMap.get(_modalmodel[i+1][j]).get(constname)+"</map>   \n");
                }
            }
            while (newitvariable.hasNext()) {
                String variablename = newitvariable.next();
                innerComponent.append("      <map key=\""+variablename+"\">"+variablename+"</map>   \n");                
            }
            
            HashMap<Transition, String> _guard = new HashMap<Transition, String>();
            _guard = _changedsignallabelMap.get(_modalmodel[i+1][0]);
            
            if(_guard.size() == 0)
            {}else {
                Set<Transition> guardtrans = _guard.keySet();
                Iterator<Transition> itguard = guardtrans.iterator();
                while (itguard.hasNext()) {
                    String guardname = _guard.get(itguard.next());
                    innerComponent.append("      <map key=\""+guardname+"\">"+guardname+"</map>  \n");          
                }
            }
            
            innerComponent.append("    </bind>   \n");
            networkComponent.append(innerComponent);
        }
        networkComponent.append("    <bind component=\"timer_template\" as=\"timer\" x=\"238.0\" y=\"296.0\">  \n");
        networkComponent.append("      <map key=\"t\">t</map>  \n");
        networkComponent.append("    </bind>  \n");
        networkComponent.append("  </component>    \n");
        
        return networkComponent.toString();
    }
    
    
    private static ArrayList<String> _prescanSystemSignal(CompositeActor model,HashMap<String,  VariableInfo> _uselessvariable) throws IllegalActionException,
            NameDuplicationException {

        Positionnum = 0;
        
        ArrayList<String> subSystemNameList = new ArrayList<String>();
        
        HashMap<String, String> _const = new HashMap<String, String>();
        List<String> _integrator = new ArrayList<String>();
        List<String> _innerguard = new ArrayList<String>();
        
        for (Iterator actors = (((CompositeActor) model).entityList())
                .iterator(); actors.hasNext();) {
            Entity innerEntity = (Entity) actors.next();
            if (innerEntity instanceof FSMActor) {
                
                HashMap<String, VariableInfo> _variableInfo = new HashMap<String, SpaceExUtility.VariableInfo>();
                
                FSMActor innerFSMActor = (FSMActor) innerEntity;
                
                _decideStateVariableSet(innerFSMActor,_variableInfo);
                
            } 
            else if (innerEntity instanceof ModalModel) {
                
                HashMap<String, VariableInfo> _variableInfo = new HashMap<String, SpaceExUtility.VariableInfo>();
                _integratorHash = new HashMap<String, List<String>>();
                _levelcross = new HashMap<String, List<String>>();
                ++ModalModelnum;
                
                _modalmodel[ModalModelnum][0] = innerEntity.getName();

                ArrayList<String> subsubSystemNameList = new ArrayList<String>();

                // If innerEntity is an instance of a ModalModel,
                // we need to perform a recursive scan of the
                // signal in the lower level.
                //
                // This includes the controller, and all rest FSMActors
                // or ModalModels in the state refinement.

                FSMActor controller = ((ModalModel) innerEntity)
                        .getController();
                controller.setName(innerEntity.getName());
                Iterator states = controller.entityList().iterator();

                while (states.hasNext()) {
                    NamedObj state = (NamedObj) states.next();
                    if (state instanceof State) {
                        String refinementList = ((State) state).refinementName
                                .getExpression();
                        if ((refinementList == null)
                                || (refinementList.equalsIgnoreCase(""))) {
                        } else {
                            // There is refinement in this state
                            for(int m = 0 ;m <= _modalmodel[ModalModelnum].length;m++)
                            {
                                
                                if(_modalmodel[ModalModelnum][m].length() == 0)
                                    {
                                        Positionnum = m;
                                        break;
                                    }
                                
                            }
                            
                            TypedActor[] refinementSystemActors = ((State) state)
                                    .getRefinement();
                            if (refinementSystemActors != null) {
                                if (refinementSystemActors.length == 1) {
                                    // It would only have the case where
                                    // actor.length == 1.
                                    // If we encounter cases > 1, report error
                                    // for further bug fix.
                                    _modalmodel[ModalModelnum][Positionnum] = refinementSystemActors[0].getName();
                                    
                                    TypedActor innerActor = refinementSystemActors[0];
                                    if (innerActor instanceof FSMActor) {
                                        FSMActor innerFSMActor = (FSMActor) innerActor;
                                        
                                        _decideStateVariableSet(innerFSMActor,_variableInfo);

                                    } else if (innerActor instanceof CompositeActor) {
                                        // First see if its director is CT.
                                        // If not, then it is beyond our current
                                        // processing scope.
                                        Director director = ((CompositeActor) innerActor)
                                                .getDirector();
                                        if (!(director instanceof ContinuousDirector)) {
                                            // This is not what we can process.
                                            throw new IllegalActionException(
                                                    "SpaceExUtility._prescanSystemSignal() clashes:\n"
                                                            + "Inner director not CT.");
                                        } else {
                                            // This is OK for our analysis
                                            // Generate system description
                                            // for these two.

                                            ArrayList<String> subsubsubSystemNameList = _prescanSystemSignal(
                                                    (CompositeActor) innerActor,_variableInfo);
                                            for (int j = 0; j < subsubsubSystemNameList
                                                    .size(); j++) {
                                                subsubSystemNameList
                                                        .add(subsubsubSystemNameList
                                                                .get(j));
                                            }
                                        }
                                    } else {
                                        // We are not able to deal with it.
                                        // Simply omit those cases.
                                    }

                                } else {
                                    // Theoretically this should not happen.
                                    // Once this happens, report an error to
                                    // notify the author the situation.
                                    throw new IllegalActionException(
                                            "SMVUtility._prescanSystemSignal() clashes: \n"
                                                    + "Refinement has two or more inner actors.");
                                }
                            }
                            
                        }
                    }
                }
                _decideStateVariableSet(controller,_variableInfo);
                
                String modalmodelname = innerEntity.getName().replace(" ", "");
                _variableInfoMap.put(modalmodelname, _variableInfo);
                _integratorMap.put(innerEntity.getName(), _integratorHash);
                _levelcrossMap.put(innerEntity.getName(), _levelcross);
                
            }
            else if (innerEntity instanceof Integrator){
                // If innerEntity is an instance of a Integrator,
                // we need to ergodic its ports and get derivative relation
               String deriValue = null,stateValue = null;
               Integrator entity = (Integrator)innerEntity;
               Iterator<?> ports = entity.portList().iterator();
               
               while (ports.hasNext()) {
                   Port port = (Port) ports.next();

                   List<Port> farport = port.connectedPortList();
                   
                   
                   if(port.getName().equals("state"))
                   {
                       //for "state" port,we can get the left value in derivative 
                       //formula,the refinementPort or the last entity
                       
                       Iterator<Port> sinkport = farport.iterator();
                       Entity PortEntity = null;
                       while(sinkport.hasNext())
                       {
                           Port statePort = sinkport.next();
                           PortEntity = (Entity)statePort.getContainer();
                           if(statePort instanceof RefinementPort)
                           {
                               stateValue = statePort.getName();
                           }else if(statePort instanceof TypedIOPort)
                           {
                           }
                       }
                       if(stateValue.length() == 0)
                           stateValue = PortEntity.getName();
                   }
                   else if (port.getName().equals("derivative")) 
                   {
                       //for "derovative" port,we can get the right value in derivative 
                       //formula,the refinementPort or the next entity
                       Iterator<Port> sourceport = farport.iterator();
                       while(sourceport.hasNext())
                       {
                           Port deriPort = sourceport.next();
                           if(deriPort instanceof TypedIOPort)
                           {
                               Entity PortEntity = (Entity)deriPort.getContainer();
                               Iterator<?> innerports = PortEntity.portList().iterator();
                               
                               while (innerports.hasNext()) {
                                   IOPort inport = (IOPort) innerports.next();
                                   if(inport.getName().equals("state") || inport.getName().equals("output"))
                                   {
                                       List<Port> innerfarport = port.connectedPortList();
                                       Iterator<Port> innersinkport = innerfarport.iterator();
                                       
                                       while (innersinkport.hasNext())
                                       {
                                           Port innerRefinementPort = innersinkport.next();
                                           if (innerRefinementPort instanceof RefinementPort) {
                                               deriValue = innerRefinementPort.getName(); 
                                           }
                                      }
                                       if(deriValue == null)
                                           deriValue = PortEntity.getName();
                                   }
                              }
                           }
                       }
                   }
               }
               if(stateValue != null && deriValue != null)
               {
                   String formular = stateValue+"' == "+deriValue;
                   _integrator.add(formular);
               }
               _integratorHash.put(model.getName(), _integrator);
            }           
            else if (innerEntity instanceof Const) {
                // If innerEntity is an instance of a Const,
                // we need to store its name and value.
                Const cvalue = (Const)innerEntity;
                _const.put(cvalue.getName(),cvalue.value.getExpression());
                _uselessvariable.put(cvalue.getName(), new VariableInfo(cvalue.value.getExpression()));
            }
            else if(innerEntity instanceof LevelCrossingDetector)
            {
                // If innerEntity is an instance of a LevelCrossingDetector,
                //we can get the innerguard it means.
                String sourceName = null;
                LevelCrossingDetector lcDetector = (LevelCrossingDetector)innerEntity;
                String direction = lcDetector.direction.getExpression();
                                
                String value = lcDetector.value.getValueAsString();
                
                IOPort trigger = lcDetector.trigger;
                List<Port> farport = trigger.connectedPortList();
                
                Iterator<Port> sourceport = farport.iterator();
                Entity PortEntity = null;
                while(sourceport.hasNext())
                {
                    Port deriPort = sourceport.next();
                    PortEntity = (Entity)deriPort.getContainer();
                    if(deriPort instanceof RefinementPort)
                    {
                        sourceName = deriPort.getName();
                    }
                    
                }
                if(sourceName.length() == 0)
                    sourceName = PortEntity.getName();
                
                switch (direction) {
                case "falling":
                    _innerguard.add(sourceName+" &gt;= "+value);
                    break;
                case "rising":
                    _innerguard.add(sourceName+" &lt;= "+value);
                    break;
                case "both":
                    _innerguard.add(sourceName+" <>"+value);
                    break;
                default:
                    break;
                }
                _levelcross.put(model.getName(), _innerguard);
            }
        }
        _constMap.put(model.getName(), _const);

        
        
        return subSystemNameList;

    }
    
    
   
    private static void _decideStateVariableSet(FSMActor actor,HashMap<String,  VariableInfo> _variableInfo) throws IllegalActionException {

        
        HashSet<State> stateSet = new HashSet<State>();
        HashMap<String, String> _const = new HashMap<String, String>();
        
        HashMap<String, String> _setInfo = new HashMap<String, String>();
        HashMap<String, State> frontier = new HashMap<String, State>();

        HashMap<String, List<String>> innerguard = new HashMap<String, List<String>>();
        
        State stateInThis = actor.getInitialState();
        String name = stateInThis.getName();
        frontier.put(name, stateInThis);
         
        HashMap<Transition,String> _guardExpr = new HashMap<Transition, String>();
        
        while (!frontier.isEmpty()) {
            // pick a state from frontier. It seems that there isn't an
            // easy way to pick an arbitrary entry from a HashMap, except
            // through Iterator
            Iterator<String> iterator = frontier.keySet().iterator();
            name = (String) iterator.next();
            stateInThis = (State) frontier.remove(name);
            if (stateInThis == null) {
                throw new IllegalActionException("Internal error, removing \""
                        + name + "\" returned null?");
            }
            ComponentPort outPort = stateInThis.outgoingPort;
            Iterator transitions = outPort.linkedRelationList().iterator();

            while (transitions.hasNext()) {
                Transition transition = (Transition) transitions.next();

                State destinationInThis = transition.destinationState();
                State sourceInThis = transition.sourceState();
                
               
                if (!stateSet.contains(destinationInThis)) {
                    frontier
                            .put(destinationInThis.getName(), destinationInThis);
                    stateSet.add(destinationInThis);
                }

                // get transitionLabel, transitionName and relation
                // name for later use. Retrieve the transition
                String SourcerefinementList = ((State) sourceInThis).refinementName
                        .getExpression();
                String DestrefinementList = ((State) destinationInThis).refinementName
                        .getExpression();
                
              //To filter the transition that source are refinement state
                if ((SourcerefinementList == null)
                        || (SourcerefinementList.equalsIgnoreCase(""))) {
                } else {
                    
                    String guard = transition.getGuardExpression();
                    if ((guard != null) && !guard.trim().equals("")) {
                        if(SourcerefinementList != "" && DestrefinementList != "")
                            {
                                _guardExpr.put(transition, guard);
                                
                            }
                            _generateGuardVariableSet(actor,transition,guard,_const,_variableInfo,innerguard);
                    }
    
                    String expression = transition.setActions.getExpression();
                    if ((expression != null) && !expression.trim().equals("")) {
                        // Retrieve possible value of the variable
                        String[] splitExpression = expression.split(";");
                        for (int i = 0; i < splitExpression.length; i++) {
                            String[] characters = splitExpression[i].split("=");
                            if (characters.length >= 1) {
                                String lValue = characters[0].trim();
                                if (Pattern.matches("^(([0-9]+\\.[0-9]*[1-9][0-9]*)|([0-9]*[1-9][0-9]*" +
                                        "\\.[0-9]+)|([0-9]*[1-9][0-9]*))$",characters[1]
                                        .trim()) == true) {
                                    double numberRetrival = Double
                                            .parseDouble(characters[1].trim());
                                    // add it into the _variableInfo
                                    VariableInfo variable = (VariableInfo) _variableInfo
                                            .get(lValue);
                                    String[] wholeValue = lValue.split("\\.");
                                    if(wholeValue.length>1)
                                    {
                                        String newEX = splitExpression[i].replace(lValue, wholeValue[1].trim());
                                        splitExpression[i] = newEX;
                                    }
                                    
                                    if(variable == null)
                                    {
                                        VariableInfo newVariable = new VariableInfo(
                                                Double.toString(numberRetrival));
                                       _variableInfo.put(lValue, newVariable);
                                    }else {
                                        _variableInfo.remove(lValue);
                                        VariableInfo newVariable = new VariableInfo(
                                                Double.toString(numberRetrival));
                                       _variableInfo.put(lValue, newVariable);
                                    }                               
                                }
                                else{
                                    String[] wholeValue = lValue.split("\\.");
                                    if(wholeValue.length == 2)
                                    {
                                       //Deal with the formula like: Cred.count =count
                                        String newEX = splitExpression[i]
                                                .trim().replace(lValue, wholeValue[1].trim());
                                        splitExpression[i] = newEX;
                                    }else if (wholeValue.length == 3) {
                                        //Deal with the formula like: cooling.Integrator.initialState = temp
                                        String portvalue = "";
                                        
                                        for (Iterator actors = (((FSMActor) actor).entityList())
                                                .iterator(); actors.hasNext();) {
                                            Entity innerEntity = (Entity) actors.next();
                                            if(innerEntity.getName().equals(wholeValue[0]))
                                            {
                                                if (innerEntity instanceof State) {
                                                    String refinementList = ((State) innerEntity).refinementName
                                                            .getExpression();
                                                    if ((refinementList == null)
                                                            || (refinementList.equalsIgnoreCase(""))) {
                                                    } else {
                                                        TypedActor[] refinementSystemActors = ((State) innerEntity)
                                                                .getRefinement();
                                                        if (refinementSystemActors != null) {
                                                            if (refinementSystemActors.length == 1) {                                    
                                                                TypedActor innerActor = refinementSystemActors[0];
                                                                if (innerActor instanceof CompositeActor) {
                                                                    for (Iterator itactor = (((CompositeActor) innerActor).entityList())
                                                                            .iterator(); itactor.hasNext();) {
                                                                    Entity innerinnerEntity = (Entity) itactor.next();
                                                                    if (innerinnerEntity.getName().equals(wholeValue[1])) {
                                                                        
                                                                        Integrator entity = (Integrator)innerinnerEntity;
                                                                        Iterator<?> ports = entity.portList().iterator();   
                                                                        while (ports.hasNext()) {
                                                                            Port port = (Port) ports.next();

                                                                            List<Port> farport = port.connectedPortList();
                                                                            
                                                                            
                                                                            if(port.getName().equals("state") || port.getName().equals("output") )
                                                                            {
                                                                                Iterator<Port> sinkport = farport.iterator();
                                                                                while(sinkport.hasNext())
                                                                                {
                                                                                    Port statePort = sinkport.next();
                                                                                    if(statePort instanceof RefinementPort)
                                                                                    {
                                                                                        portvalue = statePort.getName();
                                                                                    }else if(statePort instanceof TypedIOPort)
                                                                                    {
                                                                                        
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
                                                }
                                            }   
                                        }        
                                        String newEX = splitExpression[i]
                                                .trim().replace(lValue, portvalue);
                                        splitExpression[i] = newEX;
                                        lValue = portvalue;
                                        
                                    }
                                     
                                    String property = null;
                                    
                                    String[] propertyList = null;
                                    String[] characterOfSubGuard = characters[1].split("[-]|[*]|[+]|[/]");
                                    for (int j = 0; j < characterOfSubGuard.length; j++) {
                                        boolean initialValueExist = true;
                                        try {
                                            propertyList = actor.getAttribute(characterOfSubGuard[j].trim()).description()
                                                    .split(" ");
                                        } catch (Exception ex) {
                                            initialValueExist = false;
                                            Port signal = actor.getPort(characterOfSubGuard[j].trim());
                                            if(signal != null)
                                            {
                                                _variableInfo.put(characterOfSubGuard[j].trim(), new VariableInfo(""));
                                            }
                                        }
                                        if (initialValueExist == true) {
                                            // Retrieve the value of the variable. Property contains
                                            // a huge trunk of string content, and only the last variable is
                                            // useful.
                                            property = propertyList[propertyList.length - 1];
                                            VariableInfo variableInfo = (VariableInfo) _variableInfo
                                                    .get(characterOfSubGuard[j].trim());
        
                                            if (Pattern.matches("^(([0-9]+\\.[0-9]*[1-9][0-9]*)|([0-9]*[1-9][0-9]*" +
                                                            "\\.[0-9]+)|([0-9]*[1-9][0-9]*))$", property) == true) {
                                                
                                                _const.put(characterOfSubGuard[j].trim(), property);
                                            }
                                            if (variableInfo != null && (characterOfSubGuard[j].trim().indexOf(".") == -1)) {}
                                            else {
                                                _variableInfo.put(characterOfSubGuard[j].trim(), new VariableInfo(property));
                                            }
                                        } else {
                                            property = "";
                                        }
                                    }
                                    if(_variableInfo.get(lValue) == null && (lValue.trim().indexOf(".") == -1))
                                    {
                                        _variableInfo.put(lValue, new VariableInfo(characters[1].trim()));
                                    } 
                                }
                            }
    
                        }
                        StringBuilder newexpression = new StringBuilder("");
                        String[] delSame = splitExpression[0].split("=");
                        
                        if(delSame.length>1)
                        {
                            if(delSame[0].trim().equals(delSame[1].trim()))
                            {}
                            else {
                                newexpression.append(splitExpression[0]);
                            }
                        }
                        
                        for(int i = 1; i<splitExpression.length;i++)
                        {
                            String[] character = splitExpression[i].split("=");
                            if(character.length>1)
                            {
                                if(character[0].trim().equals(character[1].trim()))
                                {}
                                else 
                                {
                                    if(newexpression.length() == 0)
                                        newexpression.append(splitExpression[i]);
                                    else 
                                        newexpression.append(" , "+splitExpression[i]); 
                                }
                            }
                        }
                        String setexpression = newexpression.toString();
                        setexpression = setexpression.replace("=", ":=");
                        if (setexpression.length() != 0) {
                            _setInfo.put(transition.getName(), setexpression);
                        }
                    }
                }  
            }

        }
        _constMap.put(actor.getName(), _const);
        _signalportMap.put(actor.getName(), _signalPort);
        _guardExprMap.put(actor.getName(), _guardExpr);
        _newguardMap.put(actor.getName(), innerguard);
        _setinfoMap.put(actor.getName(), _setInfo);
       
    }
    
    public static void _generateGuardVariableSet(FSMActor actor,Transition transition,String guard,
            HashMap<String, String> _const,HashMap<String,  VariableInfo> _variableInfo,HashMap<String, List<String>> innerguard)
    {
        
        List<String> _guardInfo = new ArrayList<String>();
        String[] guardSplitExpression = guard.split("(&&)");
        if (guardSplitExpression.length != 0) {
            for (int i = 0; i < guardSplitExpression.length; i++) {

                String subGuardCondition = guardSplitExpression[i]
                        .trim();
                
                String[] characterOfSubGuard = subGuardCondition
                        .split("(>=)|(<=)|(==)|(!=)|[><]");
                // Here we may still have two cases:
                // (1) XXX_isPresent (2) the normal case.
                boolean b = Pattern.matches(".*_isPresent",
                        characterOfSubGuard[0].trim());
                if(subGuardCondition.equals("true"))
                    continue;
                if (b == true) {
                    String present = characterOfSubGuard[0].trim().replace("_isPresent", "");
                    
                    Port signal = actor.getPort(present);
                        
                    if (signal != null) 
                    {
                        boolean temp = true; 
                        for (int j = 0; j < _signalPort.size(); j++) {
                            if(present.equals(_signalPort.get(j)))
                                temp = false;
                        }
                        if(temp)
                            _signalPort.add(present);
                    }
                }
                   else {
                    

                    String lvalue = characterOfSubGuard[0]
                            .trim();
                    String attribute = "";
                    if(lvalue.contains("(")){
                    attribute=lvalue.substring(lvalue.indexOf("(")+1);
                    attribute = attribute.substring(0, attribute.indexOf(")"));
                    }
                    else {
                        attribute = lvalue;
                    }
                    
                    guard = guard.replace(lvalue.trim(), attribute.trim());
                    
                    if (actor.getAttribute(attribute) != null) {
                        
                    }
                    else {
                        if (Pattern.matches("^(([0-9]+\\.[0-9]*[1-9][0-9]*)|([0-9]*[1-9][0-9]*" +
                                "\\.[0-9]+)|([0-9]*[1-9][0-9]*))$", characterOfSubGuard[1].trim()) == true) {
                            subGuardCondition = subGuardCondition.replace(
                                    subGuardCondition.substring(subGuardCondition.indexOf(lvalue),lvalue.length()+1),attribute);
                            
                            if(_variableInfo.get(attribute) == null)
                            {
                                _variableInfo.put(attribute, new VariableInfo(characterOfSubGuard[1].trim()));
                            }                         
                        }
                        else {
                            String property = null;
                            boolean initialValueExist = true;
                            String[] propertyList = null;
                            try {
                                propertyList = actor.getAttribute(characterOfSubGuard[1].trim()).description()
                                        .split(" ");
                            } catch (Exception ex) {
                                initialValueExist = false;
                                
                                Port signal = actor.getPort(characterOfSubGuard[1].trim());
                                if(signal != null && _variableInfo.get(signal) == null)
                                {
                                    _variableInfo.put(characterOfSubGuard[1].trim(), new VariableInfo(""));
                                }
                            }
                            if (initialValueExist == true) {
                                // Retrieve the value of the variable. Property contains
                                // a huge trunk of string content, and only the last variable is
                                // useful.
                                property = propertyList[propertyList.length - 1];
                                VariableInfo variableInfo = (VariableInfo) _variableInfo
                                        .get(characterOfSubGuard[1].trim());

                                if (Pattern.matches("^(([0-9]+\\.[0-9]*[1-9][0-9]*)|([0-9]*[1-9][0-9]*" +
                                		"\\.[0-9]+)|([0-9]*[1-9][0-9]*))$", property) == true) {
                                    
                                    String consts = (String)_const.get(characterOfSubGuard[1]);
                                    if (consts == null) {
                                        _const.put(characterOfSubGuard[1].trim(), property);
                                    }
                                    
                                    if(_variableInfo.get(attribute) == null)
                                    {
                                        _variableInfo.put(attribute, new VariableInfo(characterOfSubGuard[1].trim()));
                                    }                          
                                    if (variableInfo != null) {}
                                    else {
                                        _variableInfo.put(characterOfSubGuard[1].trim(), new VariableInfo(property));
                                    }
                                }
                            } else {
                                
                                Port signal = actor.getPort(attribute);
                                if(signal != null && _variableInfo.get(signal) == null)
                                {
                                    _variableInfo.put(attribute.trim(), new VariableInfo(""));
                                }
                                property = "";
                            }
                            
                        }                     
                    }
                }
            }
            guard = guard.replace("&&", "&amp;");
            guard = guard.replace(">", "&gt;");
            guard = guard.replace("<", "&lt;");
            
            _guardInfo.add(guard);
        }
        boolean c = Pattern.matches(".*_isPresent",
                guard.trim());
        if(_guardInfo != null)
        {
           if(c)
               {
               _guardInfo.remove(guard);
               }
           else {
               String source = transition.sourceState().getName();  
                innerguard.put(source, _guardInfo);
                
           }
        }
   }
    
    
    
   
    //private static HashMap<String, String> _setInfo;
    
    private static HashMap<String, HashMap<String, List<String>>> _newguardMap;
    private static List<String> _signalPort;
    private static HashMap<String, List<String>> _integratorHash;
    private static HashMap<String, HashMap<Transition, String>> _guardExprMap;
    private static HashMap<String, HashMap<String, String>> _setinfoMap;
    private static HashMap<String, HashMap<String, List<String>>> _integratorMap;
    private static HashMap<String, List<String>> _levelcross;
    private static HashMap<String, HashMap<String, List<String>>> _levelcrossMap;
    private static HashMap<String, List<String>> _signalportMap; 
    private static HashMap<String, HashMap<Transition, String>> _changedsignallabelMap;
    private static HashMap<String, HashMap<String, VariableInfo>> _variableInfoMap;
    private static HashMap<String, HashMap<String, String>> _constMap;
    private static String[][] _modalmodel;
    private static int ModalModelnum = 0,Positionnum = 0;
    private final static int scope = 10; 
    
    public static class VariableInfo {
       
        private VariableInfo(String value)
        {
            valueString = value;
        }
        private String valueString;
    }
}