characteristics for successful algorithm:

Scalar Metric | Pass/Fail equivalent
------------- | ---------------------
how many of the constraints did it satisfy | did it satisfy all of the constraints?
how many feasible regions did it find | did it find all the feasible regions?
what was the variance of the distribution | was the variance above X?
was it able to produce enough points fast enough | does it make Y points-per-second?

some algorithms to test, as per George Cheng's recomendations in OPYL format:

### Simple problem: Pressure vessel ###

```
inputs:
  Ts: {lower: 1.0, upper: 1.375}
  R: {lower: 25.0, upper: 150.0}
  L: {lower: 25.0, upper: 240.0}
  Th: {lower: 0.625, upper: 1.0}
  
constraints:
  c1: Ts - 0.0193*R >= 0
  c2: Th - 0.00954*R >= 0
  c3: (pi*(R^2)*L) + ((4/3)*pi*(R^3)) - (1.296*(10^6))>0
```
  
  
### Medium problem: stepped-end beam ###

```
% lb=[0.01 0.3 0.5]; Replicated by n, number of beams
% ub=[0.05 0.65 1]; Replicated by n, number of beams

% n=10;
% E=2e11;
% P=50000;
% sigma=14000e4*2.5;
% for i=1:n
%     s1=0;
%     for j=1:i
%         s1=s1+x(3*j,:);
%     end
%     c(i,:)=6*P*s1./(x(3*i-2).*x(3*i-1).^2)-sigma;
%     c(i+n,:)=(x(3*i-1)./x(3*i-2))-25;
% end
% s2=0;
% for i=1:n
%     s2=s2+x(3*i,:).*x(3*i-1,:).*x(3*i-2,:);
% end
% c(2*n+1,:)=s2-0.4;
% %  c
% %  c1;
% %  c=[];
% ceq=[];
```

aka

```
constraints:

```


### Hard problem: P118 ###

```
% lb = [8;43;3;0;0;0;0;0;0;0;0;0;0;0;0];
% ub = [21;57;16;90;120;60;90;120;60;90;120;60;90;120;60];

% ccnt = 1;
% for i = 1:4
%     c(ccnt,:) = -x(3*i+1,:)+x(3*i-2,:)-7;
%     c(ccnt+1,:) = x(3*i+1,:)-x(3*i-2,:)-6;
%     c(ccnt+2,:) = -x(3*i+2,:)+x(3*i-1,:)-7;
%     c(ccnt+3,:) = x(3*i+2,:)-x(3*i-1,:)-7;
%     c(ccnt+4,:) = -x(3*i+3,:)+x(3*i,:)-7;
%     c(ccnt+5,:) = x(3*i+3,:)-x(3*i,:)-6;
%     ccnt = ccnt +6;
% end
% c(ccnt,:) = -x(1,:)-x(2,:)-x(3,:)+60;
% c(ccnt+1,:) = -x(4,:)-x(5,:)-x(6,:)+50;
% c(ccnt+2,:) = -x(7,:)-x(8,:)-x(9,:)+70;
% c(ccnt+3,:) = -x(10,:)-x(11,:)-x(12,:)+85;
% c(ccnt+4,:) = -x(13,:)-x(14,:)-x(15,:)+100;
% ceq = [];

For the matlab codes, dimension 1 (rows) represents variables/constraints. Dimension 2 (columns) represents points.

```