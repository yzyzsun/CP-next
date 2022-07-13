FROM node
WORKDIR /cp-next
COPY . .
ENV PATH="/cp-next/bin:${PATH}"
RUN spago build
CMD spago run
